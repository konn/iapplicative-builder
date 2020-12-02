{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE LambdaCase #-}
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
{-# LANGUAGE UndecidableSuperClasses #-}

{- | Building mechanism with static dependency graph with no cyclic dependency,
   guaranteed by indexed applicatives!
-}
module Data.Builder.Applicative.Indexed.Types
  ( Build (..),
    Build' (..),
    iterBuild,
    rule,
    rule',
    Rule (..),
    RuleF (..),
    whole,
    field,
    depends,
    interpRule,
    interpRuleA,
    embedRule,
    TaggedRule (..),
    WithArg (..),
    rules,
  )
where

import Control.Applicative
import Control.Category (Category)
import qualified Control.Category as Cat
import Data.Coerce
import Data.Functor.Identity (Identity (Identity), runIdentity)
import Data.Functor.Indexed
  ( IxApplicative (..),
    IxFunctor (..),
    IxPointed (..),
  )
import Data.Functor.Indexed.WrapCategory
import Data.HList
import Data.Kind (Type)
import Data.Membership (Absent, Lookup, Lookup', Member (..), Membership (There))
import Data.Tagged
import Data.Type.Equality
import GHC.Exts (Proxy#, proxy#)
import GHC.OverloadedLabels (IsLabel (..))
import GHC.Records (HasField (..))
import GHC.TypeLits (KnownSymbol)
import Type.Reflection ()
import Unsafe.Coerce (unsafeCoerce)

-- Must be an ordinary applicative for /fixed/ is
-- N.B. is must be type-level maps, not a list, but we use list for a sake of brevity.
data RuleF env (is :: [(k, Type)]) a where
  Depends :: forall l is env. Membership l is -> RuleF env is (Lookup' l is)
  Whole :: RuleF env is env
  Field ::
    (KnownSymbol l, HasField l env v) =>
    Proxy# l ->
    RuleF env is v

embedRule :: RuleF env is a -> Rule env is a
{-# INLINE embedRule #-}
embedRule = \fx -> MkRule $ \f -> f fx

depends :: forall l env is. Member l is => Rule env is (Lookup' l is)
{-# INLINE depends #-}
depends = embedRule $ Depends (membership @l @is)

whole :: forall a is. Rule a is a
{-# INLINE whole #-}
whole = embedRule Whole

field :: forall l env is a. (KnownSymbol l, HasField l env a) => Rule env is a
{-# INLINE field #-}
field = embedRule $ Field (proxy# :: Proxy# l)

newtype Rule env is a = MkRule
  {_runRule :: forall g. (Applicative g) => (forall x. RuleF env is x -> g x) -> g a}

instance Functor (Rule env is) where
  fmap = \f (MkRule g) -> MkRule (\x -> fmap f $ g x)
  {-# INLINE fmap #-}

instance Applicative (Rule env is) where
  pure = \x -> MkRule $ \_ -> pure x
  {-# INLINE pure #-}
  (<*>) = \(MkRule f) (MkRule x) -> MkRule $ \k -> f k <*> x k
  {-# INLINE (<*>) #-}
  liftA2 = \f (MkRule fa) (MkRule fb) -> MkRule $ \k ->
    liftA2 f (fa k) (fb k)
  {-# INLINE (*>) #-}
  (*>) = \(MkRule fa) (MkRule fb) -> MkRule $ \k ->
    fa k *> fb k
  {-# INLINE (<*) #-}
  (<*) = \(MkRule fa) (MkRule fb) -> MkRule $ \k ->
    fa k <* fb k

newtype WithArg env is a = WithArg {runWithArg :: env -> HList Tagged is -> a}

instance Functor (WithArg env is) where
  {-# SPECIALIZE instance Functor (WithArg env is) #-}
  {-# INLINE fmap #-}
  fmap = \f -> WithArg . ((f .) .) . runWithArg

instance Applicative (WithArg env is) where
  {-# SPECIALIZE instance Applicative (WithArg env is) #-}
  pure = WithArg . const . const
  {-# INLINE pure #-}
  (<*>) =
    coerce $ liftA2 @((->) env) $ (<*>) @((->) (HList Tagged is)) @a @b ::
      forall a b. WithArg env is (a -> b) -> WithArg env is a -> WithArg env is b
  {-# INLINE (<*>) #-}

interpRuleA ::
  Applicative f =>
  (forall x. RuleF env is x -> f x) ->
  Rule env is a ->
  f a
{-# INLINE interpRuleA #-}
{-# SPECIALIZE INLINE interpRuleA ::
  (forall x. RuleF env is x -> WithArg env is x) ->
  Rule env is a ->
  WithArg env is a
  #-}
interpRuleA = \go a -> _runRule a go

interpRule ::
  (forall x. RuleF env is x -> x) ->
  Rule env is a ->
  a
{-# INLINE interpRule #-}
interpRule go = runIdentity . interpRuleA (Identity . go)

data Build' env is js where
  Empty :: Build' env is is
  Define ::
    forall k v is env.
    Lookup k is ~ 'Nothing =>
    Proxy# k ->
    Rule env is v ->
    Build' env is ('(k, v) ': is)
  Node :: Build' env is ks -> Build' env ks js -> Build' env is js

(><) :: Build' env a b -> Build' env b c -> Build' env a c
{-# INLINE (><) #-}
(><) = \case
  Empty -> id
  l -> \case
    Empty -> l
    r -> Node l r

instance Category (Build' env) where
  id = Empty
  {-# INLINE id #-}
  (.) = flip (><)

newtype Build env is js a = Build {runBuild :: WrapCategory (Build' env) is js a}
  deriving newtype (Functor, IxFunctor, IxPointed, IxApplicative)

rule :: Absent l is => proxy l -> Rule env is v -> Build env is ('(l, v) ': is) ()
{-# INLINE rule #-}
rule (_ :: proxy l) = rule' @l

rule' :: forall l is env v. Absent l is => Rule env is v -> Build env is ('(l, v) ': is) ()
{-# INLINE rule' #-}
rule' = Build . WrapCategory . Define @l @v @is proxy#

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
  fromLabel = rule' @l
  {-# INLINE fromLabel #-}

newtype TaggedRule env is t a = TaggedRule {unTaggedRule :: Rule env is a}

rules :: Build env '[] js a -> HList (TaggedRule env js) js
{-# INLINE rules #-}
rules = rulesWith HNil

iterBuild ::
  forall env i j a h.
  ( forall l x z.
    Lookup l x ~ 'Nothing =>
    Proxy# l ->
    h x ->
    Rule env x z ->
    h ('(l, z) ': x)
  ) ->
  h i ->
  Build env i j a ->
  h j
{-# INLINE iterBuild #-}
iterBuild f = \hs -> go hs . runCategory . runBuild
  where
    {-# INLINE go #-}
    go :: forall is js. h is -> Build' env is js -> h js
    go = \hs -> \case
      Node l r -> go (go hs l) r
      Empty -> hs
      Define l b -> f l hs b

newtype WrapTaggedRules env is = WrapTaggedRules {unwrapTaggedRules :: HList (TaggedRule env is) is}

rulesWith ::
  forall env is js a.
  HList (TaggedRule env is) is ->
  Build env is js a ->
  HList (TaggedRule env js) js
{-# INLINE rulesWith #-}
rulesWith =
  (unwrapTaggedRules .)
    . iterBuild
      ( \_ (WrapTaggedRules hl) r ->
          WrapTaggedRules $
            mapHList (TaggedRule . shiftRule . unTaggedRule) $ TaggedRule r :- hl
      )
    . WrapTaggedRules

shiftRule ::
  forall l a1 is env x.
  Lookup l is ~ 'Nothing =>
  Rule env is x ->
  Rule env ('(l, a1) ': is) x
{-# INLINE shiftRule #-}
shiftRule = interpRuleA go
  where
    go :: forall a. RuleF env is a -> Rule env ('(l, a1) ': is) a
    {-# INLINE go #-}
    go = \case
      Depends (mem :: Membership l' is) ->
        gcastWith (unsafeCoerce $ Refl @() :: a :~: Lookup' l' ('(l, a1) ': is)) $
          embedRule $ Depends (There mem)
      Whole -> whole
      Field (_ :: Proxy# l') -> field @l'
