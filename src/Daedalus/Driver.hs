{-# Language BlockArguments #-}
{-# Language FlexibleInstances #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}

module Daedalus.Driver
  ( Daedalus
  , daedalus
  , ddlPassFromFile
  , ddlLoadModule
  , ddlGetPhaseMaybe
  , ddlGetPhase
  , ddlGetAST
  , ddlBasis
  , ddlBasisMany
  , ddlGetFNameMaybe
  , ddlGetFName

  , normalizedDecls

    -- * Compiling to Hasekell from TC
  , saveHS
  , CompilerCfg(..)
  , UseQual(..)

    -- * Various ASTs
  , ModulePhase(..)
  , astParse
  , astTC
  , astCore
  , astVM
  , astImports

    -- * Passes
  , Pass(..)
  , phasePass
  , passParse
  , passResolve
  , passTC
  , passDeadVal
  , passSpecialize
  , passCore
  , passInline
  , passStripFail
  , passSpecTys
  , passVM
  , ddlRunPass

    -- * State
  , State(..)
  , ddlState
  , ddlGet
  , ddlSetState

    -- * Options
  , ddlGetOpt
  , ddlSetOpt
  , ddlUpdOpt
  , optOutHandle
  , optSearchPath

    -- * Output
  , ddlPutStr
  , ddlPutStrLn
  , ddlPrint

    -- * Exception
  , DaedalusError(..)
  , prettyDaedalusError
  , ddlThrow

    -- * IO
  , ddlIO
  ) where

import Data.Map(Map)
import qualified Data.Map as Map
import Data.Maybe(fromMaybe)
import Data.List(find)
import Control.Monad(msum,foldM,forM,unless)
import Control.Monad.IO.Class (MonadIO(..))
import Control.Exception(Exception,throwIO)
import System.IO(Handle,hPutStr,hPutStrLn,hPrint,stdout)
import System.FilePath((</>),addExtension)
import System.Directory(createDirectoryIfMissing)
import MonadLib (StateT, runM, sets_, set, get, inBase, lift)

import Daedalus.SourceRange
import Daedalus.PP(pp)
import Daedalus.Panic(panic)
import Daedalus.Rec(forgetRecs)
import Daedalus.GUID

import Daedalus.Pass

import Daedalus.AST
import Daedalus.Type.AST
import qualified Daedalus.Type.CheckUnused as CheckUnused
import Daedalus.Module(ModuleException(..), resolveModulePath, pathToModuleName)
import Daedalus.Parser(prettyParseError, ParseError, parseFromFile)
import Daedalus.Scope (Scope)
import qualified Daedalus.Scope as Scope
import Daedalus.Type(inferRules)
import Daedalus.Type.Monad(TypeError, runMTypeM)
import Daedalus.Type.DeadVal(ArgInfo,deadValModule)
import Daedalus.Type.Free(topoOrder)
import Daedalus.Specialise(specialise)
import Daedalus.Normalise(normalise)
import Daedalus.Normalise.AST(NDecl)
import qualified Daedalus.CompileHS      as HS
import Daedalus.Compile.Config
import qualified Daedalus.Compile.LangHS as HS
import qualified Daedalus.Core as Core
import qualified Daedalus.Core.Inline as Core
import qualified Daedalus.Core.Normalize as Core
import qualified Daedalus.Core.NoMatch as Core
import qualified Daedalus.Core.StripFail as Core
import qualified Daedalus.Core.SpecialiseType as Core
import qualified Daedalus.DDL2Core as Core
import qualified Daedalus.VM   as VM
import qualified Daedalus.VM.Compile.Decl as VM
import Daedalus.PrettyError(prettyError)


---------------------------------------------------------------------------------- Convenient functions


-- | Do a specific pass, but using a file name instead of the module name.
-- The module name is computed from the file path, and the directory of
-- the file is temporarily added to the search path.
ddlPassFromFile ::
  (ModuleName -> Daedalus ()) ->
  FilePath -> Daedalus ModuleName
ddlPassFromFile pass file =
  do let (dir,m) = pathToModuleName file
     search <- ddlGetOpt optSearchPath
     ddlUpdOpt optSearchPath (dir :)
     pass m
     ddlSetOpt optSearchPath search
     pure m



-- | Do all front end-passes for this module and its dependencies.
ddlLoadModule :: ModuleName -> Daedalus ()
ddlLoadModule = passDeadVal


-- | Get the phase assocaited with the given module, if any.
ddlGetPhaseMaybe :: ModuleName -> Daedalus (Maybe ModulePhase)
ddlGetPhaseMaybe m =
  do mp <- ddlGet loadedModules
     pure $! Map.lookup m mp

-- | Get the phase assocaited with the given module.
-- Panics if the module is not present.
ddlGetPhase :: ModuleName -> Daedalus ModulePhase
ddlGetPhase m =
  do mb <- ddlGetPhaseMaybe m
     case mb of
       Just ph -> pure ph
       Nothing -> panic "ddlGetPhase" [ "Missing module", show (pp m) ]

-- | Get the AST associtated with the given module name.
-- Panics if the module is missing or its AST does not match the expectation.
ddlGetAST :: ModuleName -> (ModulePhase -> Maybe a) -> Daedalus a
ddlGetAST m ast =
  do ph <- ddlGetPhase m
     case ast ph of
       Just x   -> pure x
       Nothing  ->
        panic "ddlTCModule" [ "Unexpected phase for", show (pp m) ]


{- | The result is all modules (transitively) this module depends on,
including itself.

  * Assumes that there are no cycles
  * Modules are returned in dependency order
  * If a dependent module is not loaded, it is treated as a module with
    no dependencies.
-}
ddlBasis :: ModuleName -> Daedalus [ModuleName]
ddlBasis m0 = ddlBasisMany [m0]


{- | The result is all modules (transitively) these module depends on,
including itself.

  * Assumes that there are no cycles
  * Modules are returned in dependency order
  * If a dependent module is not loaded, it is treated as a module with
    no dependencies.
-}

ddlBasisMany :: [ModuleName] -> Daedalus [ModuleName]
ddlBasisMany ms0 =
  do (ms,_) <- foldM sim (Map.empty,0 :: Int) ms0
     pure $ Map.elems
          $ Map.fromList [ (t,m) | (m,t) <- Map.toList ms ]
  where
  sim s m =
    if Map.member m (fst s)
      then pure s
      else
        do mb <- ddlGetPhaseMaybe m
           let deps = maybe [] astImports mb
           (done1,t1) <- foldM sim s deps
           pure (Map.insert m t1 done1, t1 + 1)



--------------------------------------------------------------------------------

-- | Errors
data DaedalusError =
    AParseError  ParseError
  | AModuleError ModuleException
  | AScopeError  Scope.ScopeError
  | ATypeError   TypeError
  | ASpecializeError String
  | ADriverError String
    deriving Show

--------------------------------------------------------------------------------

instance Exception DaedalusError

prettyDaedalusError :: DaedalusError -> IO String
prettyDaedalusError err =
  case err of
    AModuleError e -> justShow e
    ATypeError e   -> justShow e
    AParseError e  -> prettyParseError e
    AScopeError e  ->
      case e of
        Scope.ScopeViolation _ x ->
          prettyError (sourceFrom (range x)) (show (pp e))
        _ -> justShow e
    ASpecializeError e -> pure e
    ADriverError e -> pure e
 where
  justShow it = pure (show (pp it))

--------------------------------------------------------------------------------




data State = State
  { searchPath    :: [FilePath]
    -- ^ Look for modules in these root directories

  , outHandle     :: Handle
    -- ^ This is where we say things


  , moduleFiles  :: Map ModuleName FilePath
    -- ^ For each module, the file we used to load it.

  , loadedModules :: Map ModuleName ModulePhase
    -- ^ Modules, in various stages of processing.

  , moduleDefines :: Map ModuleName Scope
    -- ^ The identifiers defined by each module.

  , ruleTypes     :: Map Name (Poly RuleType)
    -- ^ Types of rules from all typechecked modules

  , declaredTypes :: Map TCTyName TCTyDecl
    -- ^ Types declared in all typechecked modules

  , matchingFunctions :: Map Name ArgInfo -- XXX: ArgInfo is not a good name
    -- ^ Information about a variant of a rule that does not
    -- construct a semantic value, and how to call it.

  , coreTopNames :: Map Name Core.FName
    -- ^ Maps top-level value names to core names.

  , coreTypeNames :: Map TCTyName Core.TName
    -- ^ Map type names to core names.

  , nextFreeGUID :: !GUID
    -- ^ Plumb through fresh names
  }


defaultState :: State
defaultState = State
  { searchPath          = ["."]
  , outHandle           = stdout
  , moduleFiles         = Map.empty
  , loadedModules       = Map.empty
  , moduleDefines       = Map.empty
  , ruleTypes           = Map.empty
  , declaredTypes       = Map.empty
  , matchingFunctions   = Map.empty
  , coreTopNames        = Map.empty
  , coreTypeNames       = Map.empty
  , nextFreeGUID        = firstValidGUID
  }


data ModulePhase =
    ModuleInProgress                          -- ^ We are working on this
  | ParsedModule Module                       -- ^ Only parsed
  | ResolvedModule Module                     -- ^ Scoping was done
  | TypeCheckedModule (TCModule SourceRange)  -- ^ Typechecking was done
  | DeadValModule (TCModule SourceRange)      -- ^ Unused value analysis
  | SpecializedModule (TCModule SourceRange)  -- ^ Specialized
  | CoreModue Core.Module                     -- ^ Core module
  | VMModule VM.Module                        -- ^ VM module

-- | The passes, in the order they shoule happen
data Pass =
    PassParse
  | PassRessolve
  | PassTC
  | PassDeadVal
  | PassSpec
  | PassCore
  | PassVM
    deriving (Show,Eq,Ord)

phasePass :: ModulePhase -> Pass
phasePass ph =
  case ph of
    ModuleInProgress      -> panic "phasePass" ["ModuleInProgress"]
    ParsedModule {}       -> PassParse
    ResolvedModule {}     -> PassRessolve
    TypeCheckedModule {}  -> PassTC
    DeadValModule {}      -> PassDeadVal
    SpecializedModule {}  -> PassSpec
    CoreModue {}          -> PassCore
    VMModule {}           -> PassVM



-- | Get the parsed AST from a phase.
astParse :: ModulePhase -> Maybe Module
astParse ph =
  case ph of
    ParsedModule m   -> Just m
    ResolvedModule m -> Just m
    _                -> Nothing

-- | Get the typechecked AST from a phase.
astTC :: ModulePhase -> Maybe (TCModule SourceRange)
astTC ph =
  case ph of
    TypeCheckedModule tc -> Just tc
    DeadValModule tc     -> Just tc
    SpecializedModule tc -> Just tc
    _                    -> Nothing

-- | Get the Core AST from a phase
astCore :: ModulePhase -> Maybe Core.Module
astCore ph =
  case ph of
    CoreModue m -> Just m
    _           -> Nothing

-- | Get the low-level VM AST from a phase
astVM :: ModulePhase -> Maybe VM.Module
astVM ph =
  case ph of
    VMModule m -> Just m
    _          -> Nothing


-- | Get the imports of a module
astImports :: ModulePhase -> [ ModuleName ]
astImports ph =
  fromMaybe [] $
  msum [ map thingValue . moduleImports   <$> astParse ph
       , map thingValue . tcModuleImports <$> astTC    ph
       , map fromMName  . Core.mImports   <$> astCore  ph
       , map fromMName  . VM.mImports     <$> astVM    ph
       ]


-- | The Daedalus driver monad
newtype Daedalus a = Daedalus (StateT State PassM a)
  deriving (Functor, Applicative, Monad)

instance MonadIO Daedalus where
  liftIO = Daedalus . inBase . liftIO

-- | Execute a Daedalus computation starting with the "defaultState".
daedalus :: Daedalus a -> IO a
daedalus (Daedalus m) = fst <$> runM m defaultState

ddlState :: Daedalus State
ddlState = Daedalus get

ddlSetState :: State -> Daedalus ()
ddlSetState = Daedalus . set

ddlGet :: (State -> a) -> Daedalus a
ddlGet f =
  do s <- ddlState
     pure $! f s

ddlUpdate_ :: (State -> State) -> Daedalus ()
ddlUpdate_ = Daedalus . sets_

ddlIO :: IO a -> Daedalus a
ddlIO = Daedalus . inBase . liftIO

ddlThrow :: DaedalusError -> Daedalus a
ddlThrow = ddlIO . throwIO

ddlPutStr :: String -> Daedalus ()
ddlPutStr msg =
  do h <- ddlGetOpt optOutHandle
     ddlIO $ hPutStr h msg


ddlPutStrLn :: String -> Daedalus ()
ddlPutStrLn msg =
  do h <- ddlGetOpt optOutHandle
     ddlIO $ hPutStrLn h msg


ddlPrint :: Show a => a -> Daedalus ()
ddlPrint x =
  do h <- ddlGetOpt optOutHandle
     ddlIO $ hPrint h x

ddlRunPass :: PassM a -> Daedalus a
ddlRunPass = Daedalus . lift

--------------------------------------------------------------------------------
data DDLOpt a = DDLOpt (State -> a) (a -> State -> State)

ddlGetOpt :: DDLOpt a -> Daedalus a
ddlGetOpt (DDLOpt g _) = ddlGet g

ddlSetOpt :: DDLOpt a -> a -> Daedalus ()
ddlSetOpt (DDLOpt _ f) a = ddlUpdate_ \s -> f a s

ddlUpdOpt :: DDLOpt a -> (a -> a) -> Daedalus ()
ddlUpdOpt opt f =
  do a <- ddlGetOpt opt
     ddlSetOpt opt (f a)
--------------------------------------------------------------------------------


--------------------------------------------------------------------------------
-- Configuration settings

optSearchPath :: DDLOpt [FilePath]
optSearchPath = DDLOpt searchPath \a s -> s { searchPath = a }

optOutHandle :: DDLOpt Handle
optOutHandle = DDLOpt outHandle \a s -> s { outHandle = a }



--------------------------------------------------------------------------------
-- Names

ddlGetFNameMaybe :: ModuleName -> Ident -> Daedalus (Maybe Core.FName)
ddlGetFNameMaybe mname fname =
  do ents <- ddlGet (Map.toList . coreTopNames)
     let matches m = (mname,fname) == nameScopeAsModScope (fst m)
     pure (snd <$> find matches ents)

ddlGetFName :: ModuleName -> Ident -> Daedalus Core.FName
ddlGetFName m f =
    do mb <- ddlGetFNameMaybe m f
       case mb of
         Just a  -> pure a
         Nothing ->
           do nms <- ddlGet (Map.keys . coreTopNames)
              panic "ddlGetFName" $ "Unknown name"
                                  : ("module: " ++ show (pp m))
                                  : ("fun: " ++ show (pp f))
                                  : map (show . pp) nms


--------------------------------------------------------------------------------

parseModuleFromFile :: ModuleName -> FilePath -> Daedalus ()
parseModuleFromFile n file =
  do mb <- ddlIO (parseFromFile file n)
     m <- case mb of
            Left err -> ddlThrow (AParseError err)
            Right m -> pure (ParsedModule m)
     ddlUpdate_ \s ->
        s { moduleFiles   = Map.insert n file (moduleFiles s)
          , loadedModules = Map.insert n m (loadedModules s)
          }

-- | just parse a single module
parseModule :: ModuleName -> Daedalus ()
parseModule n =
  do sp     <- ddlGetOpt optSearchPath
     m_path <- ddlIO $ resolveModulePath sp n
     case m_path of
       Nothing -> ddlThrow $ AModuleError $ MissingModule n
       Just file -> parseModuleFromFile n file


-- | Do the scoping pass on a single module
resolveModule :: Module -> Daedalus ()
resolveModule m =
  do defs <- ddlGet moduleDefines
     r <- ddlRunPass (Scope.resolveModule defs m)
     case r of
       Right (m1,newDefs) ->
         ddlUpdate_ \s -> s { loadedModules = Map.insert (moduleName m1)
                                                         (ResolvedModule m1)
                                                         (loadedModules s)
                            , moduleDefines = newDefs
                            }
       Left err -> ddlThrow $ AScopeError err


-- | Typecheck this module
tcModule :: Module -> Daedalus ()
tcModule m =
  do tdefs <- ddlGet declaredTypes
     rtys  <- ddlGet ruleTypes
     r <-  ddlRunPass (runMTypeM tdefs rtys (inferRules m))
     case r of
       Left err -> ddlThrow $ ATypeError err
       Right m1 ->
         do let warn = CheckUnused.checkTCModule m1
            unless (null warn) (ppWarn warn)
            ddlUpdate_ \s -> s
              { loadedModules = Map.insert (tcModuleName m1)
                                           (TypeCheckedModule m1)
                                           (loadedModules s)
              , declaredTypes =
                  foldr (\d -> Map.insert (tctyName d) d)
                        (declaredTypes s)
                        (forgetRecs (tcModuleTypes m1))

              , ruleTypes =
                  foldr (\d -> Map.insert (tcDeclName d) (declTypeOf d))
                        (ruleTypes s)
                        (forgetRecs (tcModuleDecls m1))
              }
  where
  ppWarn xs =
    ddlPutStrLn $
      unlines
        [ prettySourceRangeLong x <>
                                " [WARNING] Statement has no effect" | x <- xs ]



analyzeDeadVal :: TCModule SourceRange -> Daedalus ()
analyzeDeadVal m =
  do mfs <- ddlGet matchingFunctions
     r <- ddlRunPass (deadValModule mfs m)
     case r of
       (m1,mfs1) -> ddlUpdate_ \s -> s
          { loadedModules = Map.insert (tcModuleName m1) (DeadValModule m1)
                                       (loadedModules s)
          , matchingFunctions = mfs1
          }

convertToVM :: Core.Module -> Daedalus ()
convertToVM m =
  do m1 <- ddlRunPass (Core.noMatch m)
     let vm = VM.compileModule m1
     ddlUpdate_ \s ->
        s { loadedModules = Map.insert (fromMName (VM.mName vm)) (VMModule vm)
                                       (loadedModules s)
          }

fromMName :: Core.MName -> ModuleName
fromMName (Core.MName x) = x



--------------------------------------------------------------------------------
-- Passes

-- | Get a module name. Never returns 'ModuleInProgress': it raises
-- `ImportLoop` instead.
getLoaded :: ModuleName -> Daedalus (Maybe ModulePhase)
getLoaded m =
  do loaded <- ddlGet loadedModules
     case Map.lookup m loaded of
       Just ModuleInProgress -> ddlThrow $ AModuleError $ ImportLoop m
       res -> pure res

-- | Like 'getLoaded', but panics if the module is missing.
doGetLoaded :: ModuleName -> Daedalus ModulePhase
doGetLoaded m =
  do mb <- getLoaded m
     case mb of
       Just ph -> pure ph
       Nothing -> panic "doGetLoaded" [ "Missing module", show (pp m) ]

-- | Specify that the current module is being processed at the moment.
inProgress :: ModuleName -> Daedalus ()
inProgress m = ddlUpdate_ \s ->
  s { loadedModules = Map.insert m ModuleInProgress (loadedModules s) }



-- | (1) Ensure that the given module is at least parsed.
-- Does not process dependencies.
passParse :: ModuleName -> Daedalus ()
passParse m =
  do mb <- getLoaded m
     case mb of
       Nothing -> inProgress m >> parseModule m
       Just _  -> pure ()

-- | (2) Ensure that the given module is at least scoped.
-- Processes the moduel's dependencies.
passResolve :: ModuleName -> Daedalus ()
passResolve m =
  do passParse m
     ph <- doGetLoaded m
     case ph of
       ParsedModule ast ->
         do inProgress m
            mapM_ (passResolve . thingValue) (moduleImports ast)
            resolveModule ast
       _ -> pure ()

-- | (3) Ensure that the given module is at least typechecked
-- Processes the moduel's dependencies.
passTC :: ModuleName -> Daedalus ()
passTC m =
  do passResolve m
     ph <- doGetLoaded m
     case ph of
       ResolvedModule ast ->
         do inProgress m
            mapM_ (passTC . thingValue) (moduleImports ast)
            tcModule ast
       _ -> pure ()

-- | (4) Replace parsing functions with matching functions when semantic values
-- are not used.
passDeadVal :: ModuleName -> Daedalus ()
passDeadVal m =
  do passTC m
     ph <- doGetLoaded m
     case ph of
       TypeCheckedModule ast ->
         do inProgress m
            mapM_ passDeadVal (astImports ph)
            analyzeDeadVal ast
       _ -> pure ()

{- | (5) Specialize for the given set of roots.
WARNING: The module name should be a new module name where we store the result
of specialization, which is different from how the other passes work. -}
passSpecialize :: ModuleName -> [(ModuleName,Ident)] -> Daedalus ()
passSpecialize tgt roots =
  do mapM_ ddlLoadModule (map fst roots)
     allMods <- ddlBasisMany (map fst roots)

     -- Find the actual Names, not just the ScopedIdents.  Pretty ugly
     let rootIds = [ ModScope m i | (m,i) <- roots ]
         -- FIXME: this ignores GUIDs
         findRootNames m = [ tcDeclName d
                           | d <- forgetRecs (tcModuleDecls m)
                           , nameScopedIdent (tcDeclName d) `elem` rootIds ]

     allDecls <- forM allMods \m ->
                    do mo <- ddlGetAST m astTC
                       pure (tcModuleTypes mo, tcModuleDecls mo, findRootNames mo)

     let (tdss,dss,rootss) = unzip3 allDecls
         tdecls = concat tdss
         decls = concat dss
         rootNames = concat rootss
         
     mb <- getLoaded tgt
     case mb of
       Just _ ->
          ddlThrow (ADriverError
                      ("Module " ++ show (pp tgt) ++ " is already loaded."))
       Nothing -> pure ()
     r <- ddlRunPass (specialise rootNames decls)
     case r of
       Left err  -> ddlThrow (ASpecializeError err)
       Right sds ->
         let ds = topoOrder sds
             mo = TCModule
                    { tcModuleName = tgt
                    , tcModuleImports = []
                    , tcModuleTypes = tdecls
                    , tcModuleDecls = ds
                    }
         in ddlUpdate_ \s -> s { loadedModules = Map.insert tgt
                                                      (SpecializedModule mo)
                                                      (loadedModules s)
                               }


-- | (6) Convert the given module to core.  For the moment, the module
-- should be one generated by the specialize pass, although in principle
-- we could allow other modules that already follow the invariant
-- ensured by specialize (i.e., no polymorphism, etc.)
passCore :: ModuleName -> Daedalus ()
passCore m =
  do mb <- getLoaded m
     mo <- case mb of
             Just (SpecializedModule mo) -> pure mo
             _ -> ddlThrow (ADriverError ("Module " ++ show (pp m) ++
                                                        " is not specialized."))
     (cm',(tnms',cnms')) <- ddlRunPass $ Core.runToCore Map.empty Map.empty
                                                            (Core.fromModule mo)
     let cm = Core.normM cm'
     ddlUpdate_ \s ->
        s { loadedModules = Map.insert (fromMName (Core.mName cm))
                                       (CoreModue (Core.normM cm))
                                       (loadedModules s)
          , coreTopNames = cnms'
          , coreTypeNames = tnms'
          }


passInline :: [Core.FName] -> ModuleName -> Daedalus ()
passInline no m =
  do ph <- doGetLoaded m
     case ph of
       CoreModue ast ->
         do i <- ddlRunPass (Core.inlineModule no ast)
            ddlUpdate_ \s ->
              s { loadedModules =
                     Map.insert m
                        (CoreModue (Core.normM i))
                        (loadedModules s) }
       _ -> panic "passInline" ["Module is not in Core form"]

passStripFail :: ModuleName -> Daedalus ()
passStripFail m =
  do ph <- doGetLoaded m
     case ph of
       CoreModue ast ->
         do ddlUpdate_ \s ->
              s { loadedModules =
                     Map.insert m
                        (CoreModue (Core.stripFailM ast)) -- FIXME: should we normM?
                        (loadedModules s) }
       _ -> panic "passInline" ["Module is not in Core form"]


passSpecTys :: ModuleName -> Daedalus ()
passSpecTys m =
  do ph <- doGetLoaded m
     case ph of
       CoreModue ast ->
         do i <- ddlRunPass (Core.specialiseTypes ast)
            ddlUpdate_ \s ->
              s { loadedModules = Map.insert m (CoreModue i) (loadedModules s) }
       _ -> panic "passSpecTys" ["Module is not in Core form"]

-- | (7) Convert to VM. The given module should be in Core form.
passVM :: ModuleName -> Daedalus ()
passVM m =
  do ph <- doGetLoaded m
     case ph of
       CoreModue ast -> convertToVM ast
       _ | phasePass ph > PassCore -> pure ()
         | otherwise -> panic "passVM" [ "Unexpected module phase"
                                       , show (phasePass ph) ]


--------------------------------------------------------------------------------

-- | Get the normalized declarations from the specialized modules.
-- It is an error if there are multiple (or none) modules that are specialized.
normalizedDecls :: Daedalus [NDecl]
normalizedDecls =
  do ms <- ddlGet loadedModules
     case [ m | SpecializedModule m <- Map.elems ms ] of
       [ mo ] -> pure (map normalise (forgetRecs (tcModuleDecls mo)))
       [] -> ddlThrow (ADriverError "There are not specialized modules.")
       xs -> ddlThrow (ADriverError ("Multiple specialized modules: " ++
                         unwords (map (show . pp . tcModuleName) xs)))


-- | Save Haskell for the given module.
-- Assumes that the module is in one of the `astTC` phases.
-- Does not do the dependencies.
-- Does not affect the state.
saveHS ::
  Maybe FilePath {- ^ Directory to save things in. -} ->
  CompilerCfg ->
  ModuleName ->
  Daedalus ()
saveHS mb cfg m =
  do ast <- ddlGetAST m astTC
     let hs = HS.hsModule cfg ast
     case mb of
       Nothing  -> ddlPrint (pp hs)
       Just dir ->
         ddlIO
         do createDirectoryIfMissing True dir
            let file = addExtension (dir </> HS.hsModName hs) "hs"
            writeFile file (show (pp hs))


