{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MagicHash #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}

{- | Building mechanism with static dependency graph with no cyclic dependency,
   guaranteed by indexed applicatives!
-}
module Data.Builder.Applicative.Indexed
  ( build,
    build',
    buildAll,
    Build,
    rule,
    rule',
    Rule,
    whole,
    field,
    depends,
  )
where

import Data.Builder.Applicative.Indexed.Types
import Data.HList (HList (..), ix)
import Data.Membership (Lookup', Member (..), Membership)
import Data.Proxy (Proxy (..))
import Data.Tagged (Tagged (..))
import GHC.Exts (Proxy#, inline)
import GHC.Records (HasField (..))
import Type.Reflection ()

build :: Member l is => proxy l -> Build env '[] is a -> env -> Lookup' l is
{-# INLINE build #-}
build (_ :: proxy l) plan env = unTagged $ ix (membership @l) $ inline buildAll env plan

build' :: forall l is env a. Member l is => Build env '[] is a -> env -> Lookup' l is
{-# INLINE build' #-}
build' = build (Proxy :: Proxy l)

-- Build everything from ground up, sequentially.
buildAll :: env -> Build env '[] js a -> HList Tagged js
{-# INLINE buildAll #-}
buildAll env = buildAllWith env HNil

buildAllWith :: forall env is js a. env -> HList Tagged is -> Build env is js a -> HList Tagged js
{-# INLINE buildAllWith #-}
buildAllWith env = go
  where
    go :: forall ks us x. HList Tagged ks -> Build env ks us x -> HList Tagged us
    {-# INLINEABLE go #-}
    go = \hl -> \case
      Rule (_l :: Proxy# l) maker ->
        let val = inline runRuleOn env hl maker
         in Tagged @l val :- hl
      (IMap _ inl) -> inline go hl inl
      (IAp l r) ->
        let hl' = inline go hl l
         in inline go hl' r
      IPure {} -> hl

runRuleOn :: forall env is a. env -> HList Tagged is -> Rule env is a -> a
{-# INLINE runRuleOn #-}
runRuleOn env built = interpRule go
  where
    {-# INLINE go #-}
    go :: RuleF env is x -> x
    go r = case r of
      Depends (mem :: Membership l is) -> unTagged $ ix mem built
      Whole -> env
      Field (_ :: Proxy# l) -> getField @l env
