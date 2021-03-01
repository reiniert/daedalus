{-# Language GADTs, ViewPatterns, PatternGuards, OverloadedStrings #-}
{-# Language GeneralizedNewtypeDeriving, ScopedTypeVariables, RankNTypes #-}

-- | Symbolically execute a fragment of DDL
module Talos.SymExec ( solverSynth
                     , symExecTy, symExecTyDecl, symExecSummary
                     ) where


import Control.Monad.Reader
import qualified Data.List.NonEmpty as NE
import qualified Data.Map as Map
import Data.Maybe (maybeToList)
import Data.Set (Set)
import qualified Data.Set as Set


-- import qualified Data.Text as T

import SimpleSMT (SExpr, Solver)
import qualified SimpleSMT as S

import Daedalus.PP
import Daedalus.Panic
import Daedalus.Type.AST hiding (tByte, tUnit, tMaybe, tMap)
import Daedalus.Type.PatComplete (CaseSummary(..))

import Talos.SymExec.ModelParser
import Talos.SymExec.Monad
import Talos.SymExec.Path
import Talos.SymExec.StdLib
import Talos.SymExec.TC

import Talos.Analysis.Domain
import Talos.Analysis.EntangledVars
import Talos.Analysis.Monad (Summary(..))
import Talos.Analysis.Slice (Slice(..), SimpleSlice(..))
import qualified Talos.Analysis.Slice as S


--------------------------------------------------------------------------------
-- Solver synthesis

solverSynth :: Solver -> SummaryClass -> TCName Value ->
               ProvenanceTag -> Slice a -> IO SelectedPath
solverSynth s cl root prov fps = S.inNewScope s $ do
  model <- S.declare s modelN tModel
  S.assert s (S.fun (mkPredicateN cl (tcName root)) [model])
  r <- S.check s
  case r of
    S.Sat -> pure ()
    -- FIXME: pretty gross
    S.Unsat   -> error "Unsat"
    S.Unknown -> error "Unknown"

  sexp <- getValue modelN  

  case evalModelP (parseModel prov fps) sexp of
    [] -> panic "No parse" []
    sp : _ -> pure sp
    
  where
    getValue :: String -> IO SExpr
    getValue a = do
      res <- S.command s $ S.fun "get-value" [S.List [S.const a]]
      case res of
        S.List [S.List [_, v]] -> pure v
        _ -> panic (unlines
                    [ "Unexpected response from the SMT solver:"
                    , "  Exptected: a value"
                    , "  Result: " ++ S.showsSExpr res ""
                    ]) []

-- This has to follow symExecSlice
parseModel :: ProvenanceTag -> Slice a ->  ModelP SelectedPath
parseModel prov = go 
  where
    go sl =
      case sl of
        SDontCare n sl'           -> dontCare n <$> go sl'
        SDo _x slL slR            -> uncurry pathNode <$> pSeq (parseNodeModel prov slL) (go slR)
        SDo_   slL slR            -> uncurry pathNode <$> pSeq (parseNodeModel prov slL) (go slR)
        SUnconstrained            -> pure Unconstrained
        SSimple (SPure {})        -> pure Unconstrained
        SSimple (SCoerceCheck {}) -> pure Unconstrained
        SSimple s                 -> pathNode <$> parseSimple <*> pure Unconstrained

    pathNode (NestedNode Unconstrained) = dontCare 1
    pathNode sp                         = PathNode sp

parseNodeModel :: ProvenanceTag -> Slice a -> ModelP SelectedNode
parseNodeModel prov = go
  where
    go sl =
      case sl of
        SSimple (SPure {})        -> pure (SimpleNested Unconstrained)
        SSimple (SCoerceCheck {}) -> pure (SimpleNested Unconstrained)
        SSimple _                 -> SelectedSimple prov <$> pBytes
        SChoice sls               -> pIndexed (\n -> SelectedChoice n <$> parseModel prov (sls !! n))
        SCase (CaseNode { caseAlts = alts, caseDefault = m_sl }) ->
          let go n | n < NE.length alts = SelectedCase n <$> parseModel prov (sAltBody (alts NE.!! n))
                   | Just sl <- m_sl  = SelectedCase n <$> parseModel prov sl
                   | otherwise = panic "Case result out of bounds" [show n]
          in pIndexed go
        SCall (CallNode { callClass = cl, callPaths = paths }) ->
          let doOne (Wrapped (_, sl)) = parseModel prov sl
          in SelectedCall cl <$> foldr1 (\fc rest -> uncurry mergeSelectedPath <$> pSeq fc rest)
                                        (map doOne (Map.elems paths))
        SMany (ManyNode { manyBody = sl }) -> do
          let psl = parseModel prov sl
              doOne l r = uncurry (:) <$> pSeq l r
          SelectedMany <$> (pIndexed $ \n -> foldr doOne (pure []) (replicate (fromIntegral n) psl))
        
        _                         -> SimpleNested <$> parseModel prov sl

-- -----------------------------------------------------------------------------
-- Types

-- -- -----------------------------------------------------------------------------
-- -- Dealing with Many
-- -- Many is modeled as a recursive function (essentially n*), and so
-- -- needs to be pulled out into a separate function.  This returns both
-- -- the list and its length
-- --
-- -- We define it slightly awkwardly as otherwise the solver doesn't terminate.
-- --
-- -- FIXME: lists now carry their length, so we could simplify here
-- defineMany :: Solver -> String -> [(String, SExpr)] -> SExpr
--            -> SParserM -> SolverM ()
-- defineMany s name args pT p = do
--   void $ do
--     st    <- freshSym "state"
--     body' <- runSParserM body (tTuple S.tInt (tListWithLength pT)) (S.const st)
--     liftIO $ S.defineFunRec s name (args ++ [(st, tState)]) (tParserM bodyT) (\_ -> body')
--   where
--     bodyT = tTuple S.tInt (tListWithLength pT)
--     body =  do st0 <- getState -- should be i from above
--                withConts (failC st0) successC p

--     -- This is a bit subtle - if o fails, we need to ignore any input
--     -- it has consumed (spure would otherwise return the current input)
--     failC st      = withInput st $ spure (sTuple (S.int 0) (sNil pT))
--     successC st x = withInput st $
--       sbind (scallP name (map (S.const . fst) args))
--             (\n_xs -> spure (sTuple (S.add (sFst n_xs) (S.int 1))
--                                     (sCons x (sSnd n_xs))))

-- -- This is a bit evil as it relies on having IO inside SParserM
-- symExecMany :: Env -> WithSem -> Commit -> ManyBounds (TC a Value) -> TC a Grammar
--             -> SParserM
-- symExecMany e ws _c bnds body = do
--   manyN <- freshGlobalSym "many"

--   -- Figure out what arguments to pass to the new procedure.  We could
--   -- just use all of env
--   let frees  = map valueName (Set.toList (tcFree bnds `Set.union` tcFree body))
--       params = map (lookupEnv e) frees
--       bodyT  = symExecTy (typeOfStripG body)

--   (e', args) <- lift . lift $ envFromParams (solver e) frees

--   -- FIXME: lift . lift
--   lift . lift $ defineMany (solver e) manyN args bodyT (symExecG e' body)

--   nres    <- S.const <$> freshSym "n"
--   boundsP <- symExecManyBounds e bnds nres

--   -- call the new function and check the bounds
--   sbind (scallP manyN params)
--         (\n_xs -> sbind (sguard (mklet nres (sFst n_xs) boundsP))
--                         (\_ -> mbPure ws (sSnd n_xs)))
--   where
--     valueName :: Some TCName -> TCName Value
--     valueName (Some n@(TCName { tcNameCtx = AValue })) = n
--     valueName _ = error "Sholdn't happen: symExecMany/valueName"

-- -- -----------------------------------------------------------------------------
-- -- Symbolic execution of loops (over lists)
-- --
-- -- As with Many, this will create a recursive function.

-- -- We translate for (acc = e; v in xs) { F frees acc v }
-- --
-- -- into
-- --
-- -- (define-fun-rec loop ( ...frees... (acc T) (xs (List t)))
-- --   (ite (is-nil xs)
-- --        acc
-- --        (let ((acc' (F frees acc (head xs))))
-- --             (loop frees acc' (tail xs)))))

-- -- defineLoop :: Solver -> String -> [(String, SExpr)]
-- --            -> String -> SExpr -> String -> SExpr
-- --            -> SParserM -> IO ()
-- -- defineLoop s name args accV accT elV elT body = do




-- --   void $ runSolverM $ do
-- --     i  <- freshSym "input"
-- --     body' <- runReaderT (body p) (SParserMArgs bodyT (S.const i))
-- --     liftIO $ S.defineFunRec s name (args ++ [(i, tInput)]) (tParserM bodyT) (\_ -> body')
-- --   where
-- --     bodyT = tTuple S.tInt (tList pT)

-- --     body p = do
-- --       p' <- local (\x -> x { sType = pT }) p
-- --       r <- S.const <$> freshSym "r"
-- --       rhs <- S.ite (S.fun "is-fail" [r])
-- --                <$> (spure (sTuple (S.int 0) (S.as (S.symbol "nil") (tList pT))))
-- --                <*> (let x = S.fun "result" [r]
-- --                     in local (\i -> i { sInput = S.fun "input" [r] })
-- --                              (sbind (N "n-xs" bodyT)
-- --                                     (scallP name (map (S.const . fst) args))
-- --                                     (\n_xs -> spure (sTuple (S.add (sFst n_xs) (S.int 1))
-- --                                                             (S.fun "insert" [x, sSnd n_xs])))))
-- --       pure (mklet r p' rhs)

-- symExecVLoop :: Env -> Loop a Value -> SParserM
-- -- FIXME: we ignore kname
-- symExecVLoop e loop@(Loop { loopFlav = Fold acc accInitE }) = do
--   loopN <- freshGlobalSym "loop"

--   -- Figure out what arguments to pass to the new procedure.
--   let bound  = Set.fromList [Some acc, Some (loopElName loop)]
--       frees  = map valueName (Set.toList (tcFree (loopBody loop) `Set.difference` bound))
--       params = map (lookupEnv e) frees

--   (e', args) <- lift . lift $ envFromParams (solver e) frees      

--   accV  <- freshSym "acc"
--   elV   <- S.const <$> freshSym "el"
--   listV <- freshSym "els"

--   f     <- symExecV (extendEnv acc (S.const accV) (extendEnv (loopElName loop) elV e')) (loopBody loop)

--   let accT = symExecTy (tcType acc)
--       elT  = symExecTy (tcType (loopElName loop))
--       body = S.ite (S.fun "is-nil" [S.const listV])
--                    (S.const accV)
--                    (mklet elV (S.fun "head" [S.const listV])
--                           (S.fun loopN (map (S.const . fst) args ++ [f, S.fun "tail" [S.const listV]])))

--   _ <- liftIO $ S.defineFunRec (solver e) loopN (args ++ [(accV, accT), (listV, tList elT)]) accT
--                                (\_ -> body)

--   -- The collection (list in this case)
--   accInit <- symExecV e accInitE
--   col     <- symExecV e (loopCol loop)

--   pure (S.fun loopN (params ++ [ accInit, S.fun "get-list" [col] ]))

--   where -- FIXME: copied from above
--     valueName :: Some TCName -> TCName Value
--     valueName (Some n@(TCName { tcNameCtx = AValue })) = n
--     valueName _ = error "Sholdn't happen: symExecMany/valueName"

-- symExecVLoop _e (Loop { loopFlav = LoopMap }) =
--   error "symExecVLoop map is unimplemented"


-- -----------------------------------------------------------------------------
-- Names
--
-- We can reuse the DDL names as the GUIDs make them unique, althouh
-- we have to use the summary class for top-level names

nameToSMTNameWithClass :: SummaryClass -> Name -> String
nameToSMTNameWithClass cl n = show (pp (nameScopedIdent n) <> "@" <> pp (nameID n) <> clPart)
  where
    clPart = case cl of
               FunctionResult -> "F"
               Assertions     -> "A"
    
-- -----------------------------------------------------------------------------
-- Symbolic execution of future path sets

-- Turn a summary into a SMT formula 
symExecSummary :: Name -> Summary -> SymExecM ()
symExecSummary fn summary = do
  -- Send the roots to the solver
  Map.foldMapWithKey (\root sl -> go (ProgramVar root) (mempty, sl)) (pathRootMap summary)  
  -- Send the argument domain fpss to the solver
  Map.foldMapWithKey go (explodeDomain (exportedDomain summary))
  where
    cl = summaryClass summary
    go ev (evs, sl) = do
      let predN     = evPredicateN cl fn ev
          ty        = typeOf ev
          hasResult = case ev of { ResultVar {} -> True; ProgramVar {} -> False }
          frees     = [ v | ProgramVar v <- Set.toList (getEntangledVars evs) ]
      defineSliceFun hasResult predN ty frees sl

mkPredicateN :: SummaryClass -> Name -> String
mkPredicateN cl root = "Rel-" ++ nameToSMTNameWithClass cl root

evPredicateN :: SummaryClass -> Name -> EntangledVar -> String
evPredicateN cl fn ev =
  case ev of
    ResultVar {} -> mkPredicateN cl fn
    ProgramVar v   -> mkPredicateN cl (tcName v)

-- Used to turn future path sets and arg domains into SMT terms.
defineSliceFun:: String -> Maybe Type -> 
                 [TCName Value] -> Slice a -> SymExecM ()
defineSliceFun predN m_resT frees sl = do
  body  <- symExecSlice (S.const modelN) sl
  withSolver $ \s -> void $ liftIO $ S.defineFun s predN args (tResult resT) body
  where
    resT    = maybe tUnit symExecTy m_resT
    args    = map (\v -> (tcNameToSMTName v, symExecTy (typeOf v))) frees
              ++ [(modelN, tModel)]
  
-- The SMT datatype looks something like this:
-- data SMTPath =
--   Bytes ByteString
--   | Branch   Int SMTPath
--   | Sequence SMTPath SMTPath

-- Define a predicate over a corresponding config.  This holds when a
-- path is valid --- a model for this (i.e. a config) tells us the
-- path and bytes.

-- FIXME: we will use the '$cfg' variable to refer to the current
-- config, and use shadowing whe updating.
modelN :: String
modelN  = "$model"

--------------------------------------------------------------------------------
-- SMT Helpers

mkAnd, mkOr :: [SExpr] -> SExpr
mkOr []  = S.bool True
mkOr [x] = x
mkOr xs  = S.orMany xs
  
mkAnd []  = S.bool True
mkAnd [x] = x
mkAnd xs  = S.andMany xs

--------------------------------------------------------------------------------
-- Model predicates

mkIsSeq :: SExpr -> SExpr
mkIsSeq model' = S.fun "(_ is seq)" [model']

mkMatch :: SExpr -> [(SExpr, SExpr)] -> SExpr
mkMatch e cs =
  S.fun "match" [ e
                , S.List [ S.List [ pat, rhs ] | (pat, rhs) <- cs ]
                ]

-- Shared between case and choice, although case doesn't strictly
-- required this (having the idx make replaying the model in
-- synthesise a bit nicer)

mkIndexed :: String -> SExpr -> SExpr -> SExpr
mkIndexed idxN model body =
  mkMatch model [ ( S.fun "indexed" [S.const idxN, S.const modelN], body)
                , ( S.const "_", S.bool False)
                ]

mkBranch :: SExpr -> [SExpr] -> SExpr
mkBranch model branches =
  mkIndexed idxN model (mkOr (zipWith mkOne [0..] branches))
  where
    mkOne n branch = S.and (S.eq (S.const idxN) (S.int n)) branch
    idxN = "$idx"
    
--------------------------------------------------------------------------------
-- Other helpers

evToRHS :: Maybe SExpr -> EntangledVar -> SExpr
evToRHS _ (ProgramVar v)          = symExecTCName v
evToRHS (Just res) (ResultVar {}) = res
evToRHS _ _                       = panic "Expected a result" []

--------------------------------------------------------------------------------
-- Embedding the Maybe monad (called Result)

failN :: String
failN = "$fail"

symPure :: SExpr -> SExpr
symPure r = S.fun "Success" [r]

symEmpty :: SExpr
symEmpty = S.const failN

symBind :: SExpr -> SExpr -> SExpr -> SExpr
symBind x lhs rhs =
  mkMatch lhs [ (S.fun "Success" [x], rhs)
              , (S.const "_", symEmpty)
              ]

symBind_ :: SExpr -> SExpr -> SExpr
symBind_ = symBind (S.const "_")

symGuard :: SExpr -> SExpr
symGuard b = S.ite b (symPure sUnit) symEmpty

--------------------------------------------------------------------------------
-- Many

-- Returns a predicate over the last argument
symExecManyBounds ::  ManyBounds (TC a Value) -> SExpr -> SExpr
symExecManyBounds (Exactly t)   v = S.eq v (symExecV t) 
symExecManyBounds (Between l h) v = mkAnd $ mBound l (S.geq v) ++ mBound h (S.leq v)
  where
    mBound Nothing  _ = []
    mBound (Just t) f = [ f (symExecV t) ]

-- We turn Many (l .. h) b into an assertion over l and h, and a call
-- into a recursive procedure for b, using tuples as a list.
symExecMany :: SExpr -> Maybe SExpr -> ManyNode a -> SymExecM SExpr
symExecMany model m_funres (ManyNode { manyBounds       = bnds
                                     , manyFrees        = evFrees
                                     , manyBody         = fps
                                     }) = do
  error "unimplemented"
  
  -- auxN <- freshSym "many"

  -- symExecBody auxN
  
  -- let bndsP = symExecManyBounds bnds count
  --     resP  = S.eq count . sArrayLen <$> resCallArgs
  --     callP = [ S.fun auxN (passArgs ++ resCallArgs ++ [S.int 0 {- i -}, model ]) ]
  --     p     = mkAnd (bndsP ++ resP ++ callP)
  
  -- pure (mkIndexed countN model p)

  -- where
  --   count  = S.const countN
  --   countN = "$count"
  --   iN = "$i"
  --   i  = S.const iN

  --   -- Dealing with optional returns
  --   (resParam, resCallArgs, m_res') = case m_res of
  --     Nothing  -> ([], [], Nothing)
  --     Just res -> ( [(resN, symExecTy (typeOf res))]
  --                 , [(evToRHS m_funres res)]
  --                 , Just (sSelectL (S.const resN) i)
  --                 )
    
  --   frees     = [ v | ProgramVar v <- Set.toList (getEntangledVars evFrees) ]

  --   -- These are passed through.
  --   passParams  = map (\v -> (tcNameToSMTName v, symExecTy (typeOf v))) frees
  --                 ++ [(countN, S.tInt)]

  --   passArgs    = map (S.const . fst) passParams
    
  --   -- c.f. symExecSlice
  --   symExecBody predN = do
  --     let varArgs = [ S.add i (S.int 1)
  --                   , S.fun "msnd" [S.const modelN]
  --                   ]

  --         resArgs  = map (S.const . fst) resParam
  --         recCallP = S.fun predN (passArgs ++ resArgs ++ varArgs)
      
  --     fpsP <- mkExists (Set.toList (assignedVars fps))
  --             . mklet modelN (S.fun "mfst" [S.const modelN])
  --             <$> futurePathSetPred (S.const modelN) m_res' fps

  --     let body = S.ite (S.lt i count)
  --                (S.and fpsP recCallP)
  --                 -- the prover can probably figure this out itself?
  --                (S.and (S.eq i count) (S.eq (S.const modelN) (S.const "munit")))

  --     let ps = passParams ++ resParam ++ [(iN, S.tInt), (modelN, tModel)]

  --     withSolver $ \s -> void $ liftIO $ S.defineFunRec s predN ps S.tBool (\_ -> body)
                             
-- FIXME: we use exists here as an implementation technique, they
-- aren't really requires as they are all assigned (well, asserted
-- equal) eventually.  It is convenient to do it this was as then we
-- can push assignments to simple nodes in e.g. Choose.  It is unclear
-- if this causes solver issues.
--
-- We do traverse the fps again, so that might be expensive
--
-- We need to be in a monad as we need aux. definitions for Many etc.
symExecSlice :: forall a. SExpr -> SExpr -> Slice a -> SymExecM SExpr
symExecSlice model resTy = bindFailN . collect model 
  where
    bindFailN = mklet failN (S.fun "as" [ S.const "Failure", tResult resTy ])
    
    collect :: SExpr -> Slice a -> SymExecM SExpr
    collect model' sl = do
      let mkRest sl' = mklet modelN (S.fun "msnd" [model']) <$> collect (S.const modelN) sl'
      --     mkRestNoModel fps' = collect' model' fps'
      
          thisModel          = S.fun "mfst" [model']
      case sl of
        SDontCare _ sl' -> collect model' sl'
        SDo x slL slR   ->
          symBind_ (symGuard (mkIsSeq model'))
                   (symBind (symExecTCName x) (symExecSlice thisModel (symExecTy (typeOf x)) slL) (mkRest slR))

        SDo_  slL slR   ->
          symBind_ (symGuard (mkIsSeq model'))
                   (symBind_ (symExecSlice thisModel (symExecTy tUnit) slL) (mkRest slR))
          
        SUnconstrained   -> symPure sUnit
        SSimple s        -> pure (mkBytes (flip goS s))


        -- HERE


        
        DontCare _ fps' -> collect model' fps'
            
        PathNode (Assertion a) fps' ->
         -- Doesn't have an associated element in the model, so we
         -- don't increment idx
          (:) (symExecAssertion a) <$> mkRestNoModel fps'
        
        PathNode (SimpleNode rv tc) fps' -> -- Binds a variable.
          (:) (mkBytes thisModel (\bytes -> symExecG bytes (evToRHS m_res rv) tc))
              <$> mkRest fps'
          
        PathNode n fps' -> (++) <$> goN thisModel n <*> mkRest fps'

    goS bytes s = error "unimplemented"
      -- case s of
      --   SPure v  -> symBind_ (symGuard (S.fun "is-nil" [bytes])) (symPure (symExecV v))
      --   SGetByte -> S.fun "getByteP" [bytes]
        
      -- TCMatch NoSem p -> -- FIXME, this should really not happen (we shouldn't see it)
      --   S.fun "exists" [ S.List [ S.List [ S.const resN, tByte ]]
      --                  , S.and (S.fun "getByteP" [rel, S.const resN]) (symExecP p (S.const resN)) ]
      -- TCMatch _s p    -> S.and (S.fun "getByteP" [rel, res]) (symExecP p res)
      
      -- TCMatchBytes _ws v ->
      --   S.and (S.eq rel res) (S.eq res (symExecV v))

      -- -- Convert a value of tyFrom into tyTo.  Currently very limited
      -- TCCoerceCheck ws (Type tyFrom) (Type tyTo) e
      --   | TUInt _ <- tyFrom, TInteger <- tyTo ->
      --       S.and (S.fun "is-nil" [rel])
      --             (if ws == YesSem then (S.fun "bv2int" [symExecV e]) else S.bool True)
      -- TCCoerceCheck _ws tyFrom tyTo _e ->
      --   panic "Unsupported types" [showPP tyFrom, showPP tyTo]
        
      -- _ -> panic "BUG: unexpected term in symExecG" [show (pp tc)]

  where
    resN = "$tres"
        
        

    -- model' is possibly a complex expression here, so it needs to be bound if it is used multipe times.
    
    -- goN :: SExpr -> FutureNode a -> SymExecM [SExpr]
    goN model' fpn =
      case fpn of
        Assertion {} -> error "futurePathSetRel Impossible"
        SimpleNode {} -> error "futurePathSetRel Impossible"

        -- We use shadowing of modelN here (mkBranch binds it)
        Choice fpss -> do
          branches <- mapM (collect (S.const modelN)) fpss
          pure [ mkBranch model' branches ]
        
        -- The idx isn't strictly required here, as we could just figure it out from the values.
        FNCase (CaseNode { caseCompleteness = _compl  -- we don't care here, we assert an alt is taken
                         , caseSummary      = summary
                         , caseTerm         = e
                         , caseAlts         = alts
                         , caseDefault      = m_def}) -> do
          let matchN    = "$match"

          altsPreds <- mapM (mkCaseAlt (S.const matchN)) (NE.toList alts)
          defPred <- case m_def of
            Nothing  -> pure []
            Just fps -> do r <- S.and (assertIsMissingLabel (S.const matchN) summary)
                                <$> collect (S.const modelN) fps
                           pure [r]
          pure [ mklet matchN (symExecV e) (mkBranch model' (altsPreds ++ defPred)) ]
          
        Call (CallNode { callClass = cl
                       , callResultAssign = m_res'
                       , callName = fn
                       , callAllArgs = args
                       , callPaths = paths }) ->
          let mkOne (ev, Wrapped (evs, _)) =
                let resArg = maybeToList (evToRHS m_res <$> m_res')
                    -- c.f. symExecDomain
                    execArg x | Just v <- Map.lookup x args = symExecV v
                              | otherwise = panic "Missing argument" [showPP x]
                    actuals = [ execArg x | ProgramVar x <- Set.toList (getEntangledVars evs) ]
                in S.fun (evPredicateN cl fn ev) (actuals ++ [S.const modelN] ++ resArg)
          in pure [ mklet modelN model'
                    ( foldr1 (\fc rest -> mkAnd [ mkIsSeq (S.const modelN)
                                                , mklet modelN (S.fun "mfst" [S.const modelN]) fc
                                                , mklet modelN (S.fun "msnd" [S.const modelN]) rest])
                      (map mkOne (Map.toList paths)))
                  ]

        FNMany mn -> (: []) <$> symExecMany model' m_res mn
        
        NestedNode fps -> collect' model' fps

    mkBytes model' bodyf =
      let bytes  = S.const "$bytes"
      in mkMatch model' [ ( S.fun "bytes" [bytes], bodyf bytes )
                        , ( S.const "_", symEmpty)
                        ]
     
    mkCaseAlt e (FNAlt { sAltPatterns = pats, sAltBody = b }) = do
      b' <- collect' (S.const modelN) b
      pure (mkExists (Set.toList (Set.unions (map patBindsSet pats)))
            (mkAnd (concatMap (relPattern e) pats ++ b')))

    -- Assert we match a pattern
    relPattern e pat =
      case pat of
        TCConPat (TCon tyName _) lbl pat' ->
          let getter = S.fun ("get-" ++ labelToField tyName lbl) [e]
          in assertLabel e tyName lbl : bindLabel getter pat'
        TCConPat {}    -> panic "Missing type name" [showPP pat]
        TCNumPat {}    -> panic "Unimplemented (number pattern)" [showPP pat]
        TCBoolPat b    -> [ S.eq e (S.bool b) ]
        TCJustPat pat'  -> S.fun "is-Just" [e] : bindLabel (S.fun "fromJust" [e]) pat'
        TCNothingPat {} -> [ S.fun "is-Nothing" [e] ]
        _               -> panic "Saw an unexpected  pat" [showPP pat]
      
    -- We assert that the expression must be of a form not matched by the other cases.
    assertIsMissingLabel e summary =
      case summary of
        UnionCase tyName _seen missing ->
          S.orMany (map (assertLabel e tyName) missing)
        MaybeCase seen ->
          mkAnd ([ S.fun "is-Nothing" [e] | Nothing `notElem` seen]
                 ++ [ S.fun "is-Just" [e] | Just () `notElem` seen]
                )
        NumberCase {} -> panic "Unimplemented (case over numbers)" []
        BoolCase seen ->
          mkAnd ([ e | True `notElem` seen] ++ [ S.not e | False `notElem` seen])

    assertLabel e tyName lbl = S.fun ("is-" ++ labelToField tyName lbl) [e]
    
    bindLabel e pat =
      case pat of
        TCVarPat v -> [ S.eq (symExecTCName v) e ]
        _          -> [] 
                               

  

mkExists :: [TCName Value] -> SExpr -> SExpr
mkExists [] b = b
mkExists xs b =
  S.fun "exists" [ S.List (map (\x -> S.List [ symExecTCName x, symExecTy (typeOf x) ]) xs)
                 , b
                 ]

symExecAssertion :: Assertion a -> SExpr
symExecAssertion (GuardAssertion tc) = symExecV tc
