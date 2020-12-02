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
{-# LANGUAGE TypeOperators #-}
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

    -- * Auxiliary
    runRuleOn,
    WithArg (..),
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
buildAllWith env = iterBuild go
  where
    go :: Proxy# l -> HList Tagged x -> Rule env x z -> HList Tagged ('(l, z) ': x)
    {-# INLINE go #-}
    go = \_ hl r -> Tagged (runRuleOn r env hl) :- hl

runRuleOn :: forall env is a. Rule env is a -> env -> HList Tagged is -> a
{-# INLINE runRuleOn #-}
runRuleOn = runWithArg . interpRuleA go
  where
    {-# INLINE go #-}
    go :: RuleF env is x -> WithArg env is x
    go r = case r of
      Depends (mem :: Membership l is) ->
        WithArg $ const $ unTagged . ix mem
      Whole -> WithArg const
      Field (_ :: Proxy# l) -> WithArg $ const . getField @l
