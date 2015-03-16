{-# LANGUAGE DeriveFunctor #-}
-- | This module provides \Transition Predicate Abstraction\[1,2]
--
--
-- [1] Transition Predicate Abstraction and Fair Termination, 
--     A. Podelski and A. Rybalchenko
-- [2] Size-Change Termination and Transition Invariants, 
--     M. Heizmann, N. D. Jones and A. Podelski
module Tct.Its.Data.TransitionAbstraction where

import Control.Monad.Trans
import Data.Maybe (catMaybes)
import Control.Monad.State.Strict
import qualified Data.Set as S

import qualified Tct.Core.Common.Pretty as PP

data Elem t = Init | Elem t deriving (Show, Functor)

type Edge s t = (Elem t, s, t)


type Abstraction m s t = s -> m t
type Transformer m s t = t -> s -> m (Maybe t)


-- | @lfp abstract transform initials transitions@
-- [2], Lemma 46 
lfp :: (PP.Pretty t, Monad m, Ord t) => Abstraction m s t -> Transformer m s t -> [s] -> [s] -> m [Edge s t]
lfp abstract transform initials transitions = do
  inits <- mapM abstractM initials
  let newS = mkNewS inits
  steps <- evalStateT (lfp' $ S.toList newS) newS
  return (inits ++ steps)
  where
    lfp' []         = return []
    lfp' (t1:queue) = do
      oldS <- get
      es   <- lift $ catMaybes `liftM` mapM (transformM t1) transitions
      let 
        newS = mkNewS es
        new  = S.toList $ newS `S.difference` oldS
      put $ oldS `S.union` newS
      lfp' (queue ++ new) >>= \es2 -> return (es2 ++ es)

    abstractM s = abstract s >>= \t -> return (Init, s, t)
    transformM t s = do
      tM <- transform t s
      case tM of
        Just t' -> return $ Just (Elem t, s, t')
        Nothing -> return Nothing
    mkNewS xs = S.fromList $ map (\(_,_,t2) -> t2) xs

