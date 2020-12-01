{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
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
import GHC.Exts (Proxy#)
import GHC.Records (HasField (..))
import Type.Reflection ()

build :: Member l is => proxy l -> Build env '[] is a -> env -> Lookup' l is
build (_ :: proxy l) plan env = unTagged $ ix (membership @l) $ buildAll env plan

build' :: forall l is env a. Member l is => Build env '[] is a -> env -> Lookup' l is
build' = build (Proxy :: Proxy l)

-- Build everything from ground up, sequentially.
buildAll :: env -> Build env '[] js a -> HList Tagged js
buildAll env = buildAllWith env HNil

buildAllWith :: env -> HList Tagged is -> Build env is js a -> HList Tagged js
buildAllWith env hl (Rule (_l :: Proxy# l) maker) =
  let val = runRuleOn env hl maker
   in Tagged @l val :- hl
buildAllWith env hl (IMap _ inl) = buildAllWith env hl inl
buildAllWith env hl (IAp l r) =
  let hl' = buildAllWith env hl l
   in buildAllWith env hl' r
buildAllWith _ hl IPure {} = hl

runRuleOn :: forall env is a. env -> HList Tagged is -> Rule env is a -> a
runRuleOn env built = interpRule go
  where
    go :: RuleF env is x -> x
    go r = case r of
      Depends (mem :: Membership l is) -> unTagged $ ix mem built
      Whole -> env
      Field (_ :: Proxy# l) -> getField @l env
