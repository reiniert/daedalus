{-# LANGUAGE GeneralizedNewtypeDeriving, PatternGuards, OverloadedStrings #-}
{-# LANGUAGE RankNTypes, StandaloneDeriving, DeriveFunctor, DataKinds #-}

module Daedalus.Scope (
  -- resolveModules,
  resolveModule, Scope(..), ScopeError(..), prettyScopeError, GlobalScope
  ) where

import Data.Functor ( ($>) )
import Data.Set(Set)
import qualified Data.Set as Set

import Data.Graph.SCC(stronglyConnComp)

import Data.Map(Map)
import qualified Data.Map as Map
import Data.Map.Merge.Lazy (preserveMissing, zipWithAMatched, mergeA)
import Control.Exception(Exception(..))

import MonadLib

import Daedalus.GUID
import Daedalus.SourceRange
import Daedalus.PP
import Daedalus.Rec

import Daedalus.AST
import Daedalus.PrettyError
import Daedalus.Pass

-- -----------------------------------------------------------------------------
-- Monad and operations 
--
-- This traversal figures out the scope of each variable, and records
-- which variables are used by each rule.  The latter information is
-- used to determine the SCCs.

data Scope =
  Scope { identScope :: Map Ident (IdentClass, Name)
         -- ^ Both function names and types (mainly bitdata)
        } deriving (Eq)

data IdentClass = IdentFun | IdentTy
  deriving (Eq)

data ScopeState = ScopeState { seenToplevelNames :: Set Name }

emptyScopeState :: ScopeState
emptyScopeState = ScopeState { seenToplevelNames = Set.empty }

--------------------------------------------------------------------------------
-- Errors

data ScopeError = ScopeViolation ModuleName Name
                | DuplicateNames ModuleName (Map Ident [Name])
                | DifferentCaseVars [Set Name]
                | RecursiveBitData  [Name]
                  deriving Show

instance PP ScopeError where
  pp (ScopeViolation _mn n) = "Undeclared variable" <+> backticks (pp n)
  pp (DifferentCaseVars vs) =
    "Different variables in pattern allternatives:" $$
      nest 2 (bullets [ sep (punctuate comma (map pp (Set.toList alt)))
                      | alt <- vs ])
  pp (DuplicateNames _mn m) = "Duplicate rules:"
                               $$ nest 2 (bullets (map mkOne (Map.toList m)))
    where
      mkOne (k, vs) = pp k <+> "declared at" <+> vcat (map (pp . nameRange) vs)
                               
  pp (RecursiveBitData ns) = "Recursive bitdata rules:"
                               $$ sep (punctuate comma (map pp ns))

instance Exception ScopeError where
  displayException = show . pp

prettyScopeError :: ScopeError -> IO String
prettyScopeError e@(ScopeViolation _m n) = prettyError (sourceFrom (nameRange n)) (show (pp e))
prettyScopeError e = pure (show (pp e))

--------------------------------------------------------------------------------
-- Monad

newtype ScopeM a = ScopeM (WithBase PassM
                            '[ ReaderT Scope
                             , StateT ScopeState
                             , ExceptionT ScopeError
                             ] a)
  deriving (Functor, Applicative, Monad)

instance HasGUID ScopeM where
  guidState f = ScopeM (inBase $ guidState f)

runScopeM :: Scope -> ScopeM a -> PassM (Either ScopeError (a, ScopeState))
runScopeM scope (ScopeM m) = runExceptionT (runStateT emptyScopeState (runReaderT scope m))

recordNameRef :: Name -> ScopeM ()
recordNameRef r
  | ModScope _ _ <- nameScopedIdent r = 
      ScopeM $ sets_ (\s -> s { seenToplevelNames = Set.insert r (seenToplevelNames s) } )
  | otherwise = pure ()

extendLocalScopeIn :: [Name] -> ScopeM a -> ScopeM a
extendLocalScopeIn ids (ScopeM m) = ScopeM (mapReader extendScope m)
  where
    extendScope s = s { identScope = foldl extendOneScope (identScope s) ids }
    extendOneScope vs n = Map.insert (nameScopeAsLocal n) (IdentFun, n) vs

makeNameLocal :: Name -> ScopeM Name
makeNameLocal n = do
  gid <- getNextGUID
  pure $ n { nameScopedIdent = Local (nameScopeAsUnknown n), nameID = gid }

getScope :: ScopeM Scope
getScope = ScopeM ask

--------------------------------------------------------------------------------
-- Entry points

type GlobalScope = Map ModuleName Scope {- ^ Maps module name to what's in scope -}

newtype ResolveM a =
  ResolveM { getResolveM ::
               WithBase PassM
               '[ StateT GlobalScope
                , ExceptionT ScopeError
                ] a }
  deriving (Functor, Applicative, Monad)

instance HasGUID ResolveM where
  guidState f = ResolveM $ inBase (guidState f)

makeNameModScope :: ModuleName -> Name -> ResolveM Name
makeNameModScope m n = do
  gid <- getNextGUID
  pure $ n { nameScopedIdent = ModScope m (nameScopeAsUnknown n), nameID = gid }

-- resolveModules :: HasGUID m => [Module] -> m (Either ScopeError [Module])
-- resolveModules ms = runExceptionT (fst <$> runStateT s0 (getResolveM go))
--   where
--     go = mapM resolveModule' ms
--     s0 = ResolveState Map.empty

resolveModule :: GlobalScope -> Module -> PassM (Either ScopeError (Module, GlobalScope))
resolveModule scope m = runExceptionT (runStateT scope (getResolveM go))
  where
    go = resolveModule' m

resolveModule' :: Module -> ResolveM Module
resolveModule' m =
  do ns' <- mapM (makeNameModScope (moduleName m) . ruleName) rs
     let namedRs = zip ns' rs
     bdns' <- mapM (makeNameModScope (moduleName m) . bdName) (moduleBitData m)
     let namedBDs = zip bdns' (moduleBitData m)
     
     ms <- ResolveM get
     scope <- moduleScope m ms namedRs namedBDs
     
     rs'  <- mkRec <$> mapM (runResolve scope) namedRs
     bds' <- (mkRec <$> mapM (runResolveBD scope) namedBDs) >>= mapM checkBDRecs
     
     pure $ m { moduleBitData = bds', moduleRules = rs' }
  where
    rs  = forgetRecs (moduleRules m)
    mkRec = map sccToRec . stronglyConnComp

    checkBDRecs :: Rec BitData -> ResolveM BitData
    checkBDRecs (NonRec v) = pure v
    checkBDRecs (MutRec vs) = ResolveM $ raise (RecursiveBitData (map bdName vs))
    
    -- FIXME: make nicer (can plumb through nextguid better)
    runResolve :: Scope -> (Name, Rule) -> ResolveM (Rule, Name, [Name])
    runResolve scope (n, r) = do
      (r', st) <- ResolveM $ (lift (lift (runScopeM scope (resolveRule r n))) >>= raises)
      return (r', n, Set.toList (seenToplevelNames st))

    runResolveBD :: Scope -> (Name, BitData) -> ResolveM (BitData, Name, [Name])
    runResolveBD scope (n, bd) = do
      (r', st) <- ResolveM $ (lift (lift (runScopeM scope (resolveBitData bd n))) >>= raises)
      return (r', n, Set.toList (seenToplevelNames st))

-- | Figure out the map from idents to resolved names for a given
-- module.  This is slightly more complex than it has to be, as we try
-- to detect all dups, not just the first.
moduleScope :: Module -> GlobalScope -> [(Name, Rule)] -> [(Name, BitData)] -> ResolveM Scope
  {- ^ All things in scope of this module, new things defined -}
moduleScope m ms rs bds =
  case runM merged Map.empty of
    ((allDs, defs'), dups) | Map.null dups -> allDs <$ (ResolveM $ sets_ (addRuleNames defs'))
    (_, dups)                 -> ResolveM $ raise (DuplicateNames (moduleName m) dups)
  where
    addRuleNames defs' = Map.insert (moduleName m) defs'
    
    merged  :: StateT (Map Ident [Name]) Id (Scope, Scope)
    merged  = do defs' <- foldM doMerge Map.empty defs
                 allDs <- foldM doMerge defs' imported
                 return (Scope allDs, Scope defs')

    doMerge = mergeA preserveMissing preserveMissing (zipWithAMatched matched)
    
    matched :: Ident -> (IdentClass, Name) -> (IdentClass, Name) ->
               StateT (Map Ident [Name]) Id (IdentClass, Name)
    matched k x y = sets_ (Map.insertWith (++) k [snd x, snd y]) $> x

    imported = [ identScope (ms Map.! thingValue i) | i <- moduleImports m ]

    -- Makes it easier to detect duplicates
    defs  = [ Map.singleton (nameScopeAsUnknown (ruleName r)) (IdentFun, n) | (n, r) <- rs ]
            ++ [ Map.singleton (nameScopeAsUnknown (bdName bd)) (IdentTy, n) | (n, bd) <- bds ]

-- -----------------------------------------------------------------------------
-- A type class for resolving names

resolveRule :: Rule -> Name -> ScopeM Rule
resolveRule r n' = do
  ps1 <- mapM resolve (ruleParams r)  
  e' <- extendLocalScopeIn (map paramName ps1) (resolve (ruleDef r))
  resT1 <- resolve (ruleResTy r)
  return (Rule { ruleName   = n'
               , ruleParams = ps1
               , ruleResTy  = resT1
               , ruleDef    = e'
               , ruleRange  = ruleRange r
               })

resolveBitData :: BitData -> Name -> ScopeM BitData
resolveBitData bd n' = do
  ctors' <- mapM (\(a, b) -> (,) a <$> resolve b) (bdCtors bd)
  return (bd { bdName   = n'
             , bdCtors  = ctors'
             })

class ResolveNames t where
  resolve :: t -> ScopeM t

instance ResolveNames a => ResolveNames [a] where
  resolve = traverse resolve

instance ResolveNames a => ResolveNames (Maybe a) where
  resolve = traverse resolve

-- This is the base case, x should be Unknown
instance ResolveNames Name where
  resolve x = do
    do scope <- getScope
       case Map.lookup (nameScopeAsUnknown x) (identScope scope) of
         Just (_cl, n) -> x { nameScopedIdent = nameScopedIdent n
                            , nameID = nameID n } <$ recordNameRef n
         Nothing -> makeNameLocal x

instance ResolveNames Expr where
  resolve (Expr r) = Expr <$> traverse resolve r

instance ResolveNames RuleParam where
  resolve p = RuleParam <$> makeNameLocal (paramName p)
                        <*> resolve (paramType p)

instance ResolveNames BitDataField where
  resolve p =
    case p of
      BDFLiteral n m_t -> BDFLiteral n <$> resolve m_t
      BDFField   l m_t -> BDFField l   <$> resolve m_t
      BDFWildcard  m_t -> BDFWildcard  <$> resolve m_t

instance ResolveNames e => ResolveNames (ExprF e) where
  resolve expr =
    case expr of
      ELiteral {}     -> pure expr
      ENothing {}     -> pure expr
      EJust e         -> EJust <$> resolve e
      EMatch e        -> EMatch <$> resolve e
      EMatch1 e       -> EMatch1 <$> resolve e
      EStruct fs      -> EStruct <$> resolveStructFields fs
      EChoiceU c e1 e2-> EChoiceU c <$> resolve e1 <*> resolve e2
      EChoiceT c fs   -> EChoiceT c <$> resolve fs
      EIn (l :> e)    -> (\x -> EIn (l :> x)) <$> resolve e
      EArray es       -> EArray    <$> resolve es
      EApp f es       -> EApp      <$> resolve f <*> resolve es
      EVar x          -> EVar      <$> resolve x
      EImplicit {}    -> pure expr
      ETry e          -> ETry      <$> resolve e
      ECase e ps      -> ECase     <$> resolve e <*> mapM resolveCasePatterns ps

      EAnyByte        -> pure expr
      EOptional c e   -> EOptional c <$> resolve e
      EMany c bnds z  -> EMany c   <$> resolve bnds <*> resolve z
      EEnd            -> pure expr
      EOffset         -> pure expr
      ECurrentStream  -> pure expr
      ESetStream x    -> ESetStream <$> resolve x
      EStreamLen x y  -> EStreamLen <$> resolve x <*> resolve y
      EStreamOff x y  -> EStreamOff <$> resolve x <*> resolve y

      EMapEmpty       -> pure expr
      EMapInsert ke ve me -> EMapInsert <$> resolve ke <*> resolve ve <*> resolve me
      EMapLookup ke me -> EMapLookup <$> resolve ke <*> resolve me

      EArrayLength ve  -> EArrayLength <$> resolve ve       
      EArrayIndex  ve ixe -> EArrayIndex <$> resolve ve <*> resolve ixe

      EFor fl mbI y b c -> do
        mbI' <- traverse makeNameLocal mbI
        y'   <- makeNameLocal y
        (fnames, fl') <-
          case fl of
            FFold x e -> do x' <- makeNameLocal x
                            e' <- resolve e
                            pure ([x'], FFold x' e')
            FMap      -> pure ([], FMap)

        let names = fnames ++ inames mbI' ++ [y']
    
        EFor fl' mbI' y'
          <$> resolve b 
          <*> extendLocalScopeIn names (resolve c)
        where
        inames x = case x of
                   Nothing -> []
                   Just i  -> [i]

      EIf be te fe    -> EIf       <$> resolve be <*> resolve te <*> resolve fe

      EHasType sig e t -> EHasType sig <$> resolve e <*> resolve t
      -- XXX: for the moment we don't have top level type names,
      -- but at some point we should probably add them, and then we'd
      -- have to resolve the type as well.

      EQuiet e        -> EQuiet    <$> resolve e
      EPure e         -> EPure     <$> resolve e
      EFail msg       -> EFail     <$> resolve msg

      EInRange e1 e2  -> EInRange  <$> resolve e1 <*> resolve e2
      ETriOp op e1 e2 e3 -> ETriOp op <$> resolve e1
                                      <*> resolve e2
                                      <*> resolve e3
      EBinOp op e1 e2 -> EBinOp op <$> resolve e1 <*> resolve e2
      EUniOp op e     -> EUniOp op <$> resolve e
      ESel e s        -> ESel      <$> resolve e <*> pure s

-- FIXME: Maybe we should make a separate 'Label' scope?
instance ResolveNames e => ResolveNames (UnionField e) where
  resolve (n :> e) = (n :> ) <$> resolve e

instance ResolveNames e => ResolveNames (ManyBounds e) where
  resolve = traverse resolve

instance ResolveNames t => ResolveNames (TypeF t) where
  resolve tf =
    case tf of
      TGrammar t -> TGrammar <$> resolve t
      TFun t1 t2 -> TFun <$> resolve t1 <*> resolve t2
      TStream    -> pure tf
      TByteClass -> pure tf
      TNum {}    -> pure tf
      TUInt t    -> TUInt <$> resolve t
      TSInt t    -> TSInt <$> resolve t
      TInteger   -> pure tf
      TBool      -> pure tf
      TUnit      -> pure tf
      TArray t   -> TArray <$> resolve t
      TMaybe t   -> TMaybe <$> resolve t
      TMap  k v  -> TMap <$> resolve k <*> resolve v

instance ResolveNames t => ResolveNames (Located t) where
  resolve t = traverse resolve t

instance ResolveNames SrcType where
  resolve ty =
    case ty of
      -- FIXME: should we treat tvs differently?
      SrcVar x   -> SrcVar  <$> resolve x
      SrcType tf -> SrcType <$> resolve tf

resolveStructFields :: ResolveNames e => [StructField e] -> ScopeM [StructField e]
resolveStructFields []       = return []
resolveStructFields (f : fs) = 
  case f of
    COMMIT r -> (COMMIT r :) <$> resolveStructFields fs
    Anon e   -> (:) <$> (Anon <$> resolve e) <*> resolveStructFields fs
    x := e   -> go (:=)  x e
    x :@= e  -> go (:@=) x e
    x :?= e  -> (:) <$> ((x :?=) <$> resolve e) <*> resolveStructFields fs
  where
    go ctor x e =
      do x'  <- makeNameLocal x
         f'  <- ctor x' <$> resolve e
         fs' <- extendLocalScopeIn [x'] (resolveStructFields fs)
         pure (f' : fs')

resolveCasePatterns :: ResolveNames e => PatternCase e -> ScopeM (PatternCase e)
resolveCasePatterns patC =
  case patC of
    PatternDefault e -> PatternDefault <$> resolve e
    PatternCase ps e
      | all (== bound) otherBound -> do
          (ps', newVss) <- unzip <$> mapM localise ps
          PatternCase ps' <$> extendLocalScopeIn (head newVss) (resolve e)
      | otherwise ->
          ScopeM $ raise
                 $ DifferentCaseVars -- (currentModule scope)
                 $ bound : otherBound

      where
      bound : otherBound = map patVars ps

      localise :: Pattern -> ScopeM (Pattern, [Name])
      localise pat =
        case pat of
          LitPattern {}  -> pure (pat, [])
          WildPattern _  -> pure (pat, [])
          ConPattern c p -> do (p', ns) <- localise p
                               pure (ConPattern c p', ns)
          VarPattern x   -> do x' <- makeNameLocal x
                               pure (VarPattern x', [x'])

      -- Variables bound by a patterns
      patVars :: Pattern -> Set Name
      patVars pat =
        case pat of
          LitPattern {}  -> Set.empty
          WildPattern {} -> Set.empty
          ConPattern _ p -> patVars p
          VarPattern x   -> Set.singleton x


