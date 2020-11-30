{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE MagicHash #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}

{- | Building mechanism with static dependency graph with no cyclic dependency,
   guaranteed by indexed applicatives!
-}
module Data.Builder.Applicative.Indexed.Types
  ( Build (..),
    rule,
    rule',
    Rule (..),
    RuleF (..),
    whole,
    field,
    depends,
    interpRule,
    interpRuleA,
  )
where

import Control.Applicative.Free (Ap, liftAp, runAp)
import Data.Functor.Coyoneda (Coyoneda, hoistCoyoneda, liftCoyoneda, lowerCoyoneda)
import Data.Functor.Identity (Identity (Identity), runIdentity)
import Data.Functor.Indexed
  ( IxApplicative (..),
    IxFunctor (..),
    IxPointed (..),
  )
import Data.Kind (Type)
import Data.Membership (Absent, Lookup, Lookup', Member (..))
import Data.Type.Equality (type (~~))
import GHC.Exts (Proxy#, proxy#)
import GHC.OverloadedLabels (IsLabel (..))
import GHC.Records (HasField (..))
import GHC.TypeLits (KnownSymbol)
import Type.Reflection ()

-- Must be an ordinary applicative for /fixed/ is
-- N.B. is must be type-level maps, not a list, but we use list for a sake of brevity.
data RuleF env (is :: [(k, Type)]) a where
  Depends :: Member l is => Proxy# l -> RuleF env is (Lookup' l is)
  Whole :: RuleF env is env
  Field ::
    (KnownSymbol l, HasField l env v) =>
    Proxy# l ->
    RuleF env is v

embedRule :: RuleF env is a -> Rule env is a
embedRule = MkRule . liftAp . liftCoyoneda

depends :: forall l env is. Member l is => Rule env is (Lookup' l is)
depends = embedRule $ Depends (proxy# :: Proxy# l)

whole :: forall a is. Rule a is a
whole = embedRule Whole

field :: forall l env is a. (KnownSymbol l, HasField l env a) => Rule env is a
field = embedRule $ Field (proxy# :: Proxy# l)

newtype Rule env is a = MkRule {_runRule :: Ap (Coyoneda (RuleF env is)) a}
  deriving newtype (Functor, Applicative)

interpRuleA ::
  Applicative f =>
  (forall x. RuleF env is x -> f x) ->
  Rule env is a ->
  f a
interpRuleA go = runAp (lowerCoyoneda . hoistCoyoneda go) . _runRule

interpRule ::
  (forall x. RuleF env is x -> x) ->
  Rule env is a ->
  a
interpRule go = runIdentity . interpRuleA (Identity . go)

-- N.B. @js@ and @is@ must be type-level maps, not a list, but we use list for a sake of brevity.
data Build env (is :: [(k, Type)]) (js :: [(k, Type)]) a where
  Rule :: Absent l is => Proxy# l -> Rule env is a -> Build env is ('(l, a) ': is) ()
  IMap :: (a -> b) -> Build env is js a -> Build env is js b
  IAp :: Build env is js (a -> b) -> Build env js ks a -> Build env is ks b
  IPure :: a -> Build env is is a

rule :: Absent l is => proxy l -> Rule env is v -> Build env is ('(l, v) ': is) ()
rule (_ :: proxy l) = Rule (proxy# :: Proxy# l)

rule' :: forall l is env v. Absent l is => Rule env is v -> Build env is ('(l, v) ': is) ()
rule' = Rule (proxy# :: Proxy# l)

instance IxFunctor (Build env) where
  imap = IMap

instance IxPointed (Build env) where
  ireturn = IPure

instance IxApplicative (Build env) where
  iap = IAp

instance
  ( js ~~ ('(l, a) ': is)
  , is ~~ is'
  , -- The above two must be ~~, *not* ~, in order to get inference work
    env ~ env'
  , b ~ ()
  , Lookup l is ~ 'Nothing
  ) =>
  IsLabel l (Rule env' is' a -> Build env is js b)
  where
  fromLabel = Rule (proxy# :: Proxy# l)
