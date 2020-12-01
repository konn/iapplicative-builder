{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE MagicHash #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}

module Data.Builder.Applicative.Indexed.Parallel
  ( buildPar,
  )
where

import qualified Algebra.Graph.AdjacencyMap.Algorithm as G
import Control.Monad.Par
import Data.Bifunctor.Joker
import Data.Builder.Applicative.Indexed
import Data.Builder.Applicative.Indexed.Dependency
import Data.Builder.Applicative.Indexed.Types
import Data.HList
import Data.Membership
import GHC.Exts (Proxy#)
import GHC.Records

buildParWith ::
  (Generate is, Member i is) =>
  (forall a. IVar a -> a -> Par ()) ->
  proxy i ->
  Build env '[] is () ->
  env ->
  Lookup' i is
buildParWith putter (_ :: proxy i) (plan :: Build env '[] is a) env = runPar $ do
  ivars <- generateA @is @(Joker IVar) $ const $ const (Joker <$> new)
  mapM_ (assign ivars) deps
  get $ runJoker $ ix (membership @i) ivars
  where
    factors = rules plan
    deps =
      G.reachable (DepRule $ SomeMembership $ membership @i @is) $
        depGraph plan

    assign :: HList (Joker IVar) is -> Dependency env is -> Par ()
    {-# INLINE assign #-}
    assign ivars dep = case dep of
      DepRule (SomeMembership (mem :: Membership l is)) -> fork $ do
        val <- evalRule @l ivars $ unTaggedRule $ ix mem factors
        putter (runJoker $ ix mem ivars) val
      DepField {} -> pure ()
      Global -> pure ()

    evalRule ::
      forall l.
      HList (Joker IVar) is ->
      Rule env is (Lookup' l is) ->
      Par (Lookup' l is)
    {-# INLINE evalRule #-}
    evalRule ivars = interpRuleA go
      where
        {-# INLINE go #-}
        go :: forall x. RuleF env is x -> Par x
        go r = case r of
          Depends mem -> get $ runJoker $ ix mem ivars
          Whole -> pure env
          Field (_ :: Proxy# f) ->
            pure $ getField @f @env env

{- | Build the given target and its transitive dependency parallely.
   Every target are calculated at most once and only reduced to whnf.

  See also 'buildParNF'
-}
buildPar ::
  (Generate is, Member i is) =>
  proxy i ->
  Build env '[] is () ->
  env ->
  Lookup' i is
buildPar = buildParWith put_
