{-# LANGUAGE GeneralizedNewtypeDeriving #-}

-- API for strategies, which say how to produce a path from a slice.

module Talos.Strategy.Monad ( Strategy(..)
                            , StratFun(..)
                            , StrategyM, StrategyMState, emptyStrategyMState
                            , runStrategyM -- just type, not ctors
                            , LiftStrategyM (..)
                            , summaries, getModule, getGFun, getParamSlice
                            , getIEnv
                            , rand, randR, randL, randPermute
                            -- , timeStrategy
                            ) where

import Control.Monad.State
import Control.Monad.Reader
import Control.Monad.Trans.Maybe
import System.Random
import Data.Foldable (find)
import qualified Data.Map as Map


import Daedalus.Core
import Daedalus.GUID
import Daedalus.Panic
import Daedalus.PP
import qualified Daedalus.Core.Semantics.Env as I
import qualified Daedalus.Core.Semantics.Decl as I

import Talos.SymExec.Path
import Talos.Analysis.Slice
import Talos.Analysis.Monad (Summaries, Summary(exportedDomain))
import Talos.Analysis.Domain (domainInvariant, domainElement)

import Talos.SymExec.SolverT (SolverT)
import Talos.Analysis.EntangledVars (EntangledVars)

-- ----------------------------------------------------------------------------------------
-- Core datatypes

-- FIXME: add: config (e.g. depth/max backtracks/etc.)

-- Gives some flexibility in how they are run.
data StratFun =
  SimpleStrat   (ProvenanceTag -> Slice -> StrategyM (Maybe SelectedPath))
  | SolverStrat (ProvenanceTag -> Slice -> SolverT StrategyM (Maybe SelectedPath))

data Strategy =
  Strategy { stratName  :: String
           , stratDescr :: Doc
           , stratFun   :: StratFun
           }

-- -----------------------------------------------------------------------------
-- Monad

data StrategyMState =
  StrategyMState { stsStdGen    :: StdGen
                   -- Read only
                 , stsSummaries :: Summaries
                 , stsModule    :: Module
                 , stsIEnv      :: I.Env
                 , stsNextGUID  :: GUID
                 }

emptyStrategyMState :: StdGen -> Summaries -> Module -> GUID -> StrategyMState
emptyStrategyMState gen ss md nguid  = StrategyMState gen ss md env0 nguid
  where
    env0 = I.evalModule md I.emptyEnv

newtype StrategyM a =
  StrategyM { getStrategyM :: StateT StrategyMState IO a }
  deriving (Functor, Applicative, Monad, MonadIO)

runStrategyM :: StrategyM a -> StrategyMState -> IO (a, StrategyMState)
runStrategyM m st = runStateT (getStrategyM m) st

-- -----------------------------------------------------------------------------
-- State access

summaries :: LiftStrategyM m => m Summaries
summaries = liftStrategy (StrategyM (gets stsSummaries))

getParamSlice :: LiftStrategyM m => FName -> SummaryClass -> EntangledVars -> m Slice
getParamSlice fn cl evs = do
  ss <- summaries
  let m_s = do
        summM <- Map.lookup fn ss
        summ  <- Map.lookup cl summM

        unless (domainInvariant (exportedDomain summ)) $
          panic "Failed domain invariant" ["At " ++ showPP fn]

        domainElement evs (exportedDomain summ)
  case m_s of
    Just sl -> pure sl
    Nothing -> panic "Missing summary" [showPP fn, showPP cl, showPP evs]

getGFun :: LiftStrategyM m => FName -> m (Fun Grammar)
getGFun f = getFun <$> liftStrategy (StrategyM (gets stsModule))
  where
    getFun md = case find ((==) f . fName) (mGFuns md) of -- FIXME: us a map or something
      Nothing -> panic "Missing function" [showPP f]
      Just v  -> v

getModule :: LiftStrategyM m => m Module
getModule = liftStrategy (StrategyM (gets stsModule))

getIEnv :: LiftStrategyM m => m I.Env
getIEnv = liftStrategy (StrategyM (gets stsIEnv))

-- -----------------------------------------------------------------------------
-- Random values

rand :: (LiftStrategyM m, Random a) => m a
rand = liftStrategy (StrategyM $ state go)
  where
    go s = let (b, g') = random (stsStdGen s) in (b, s { stsStdGen = g' })

randR :: (LiftStrategyM m, Random a) => (a, a) -> m a
randR r = liftStrategy (StrategyM $ state go)
  where
    go s = let (b, g') = randomR r (stsStdGen s) in (b, s { stsStdGen = g' })

randL :: LiftStrategyM m => [a] -> m a
randL [] = panic "randL: empty list" []
randL vs = (!!) vs <$> randR (0, length vs - 1)

randPermute :: LiftStrategyM m => [a] -> m [a]
randPermute = go
  where
    go [] = pure []
    go xs = do idx <- randR (0, length xs - 1)
               let (pfx, x : sfx) = splitAt idx xs
               (:) x <$> go (pfx ++ sfx)

-- -----------------------------------------------------------------------------
-- Class

class Monad m => LiftStrategyM m where
  liftStrategy :: StrategyM a -> m a

instance LiftStrategyM StrategyM where
  liftStrategy = id

instance LiftStrategyM m => LiftStrategyM (StateT s m) where
  liftStrategy m = lift (liftStrategy m)

instance LiftStrategyM m => LiftStrategyM (ReaderT s m) where
  liftStrategy m = lift (liftStrategy m)

instance LiftStrategyM m => LiftStrategyM (MaybeT m) where
  liftStrategy m = lift (liftStrategy m)

instance LiftStrategyM m => LiftStrategyM (SolverT m) where
  liftStrategy m = lift (liftStrategy m)


-- -----------------------------------------------------------------------------
-- Instances

instance HasGUID StrategyM where
  guidState f = StrategyM (state go)
    where
      go s = let (r, guid') = f (stsNextGUID s)
             in (r, s { stsNextGUID = guid' })

