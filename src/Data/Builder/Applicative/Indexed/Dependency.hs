{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE EmptyCase #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MagicHash #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE UndecidableSuperClasses #-}

module Data.Builder.Applicative.Indexed.Dependency
  ( depGraph,
    Dependency (..),
    SomeFieldOf (..),
    SomeMember (..),
    fieldName,
    Printable,
    strPrec,
  )
where

import qualified Algebra.Graph.AdjacencyMap as G
import Control.Applicative
import Data.Builder.Applicative.Indexed.Types
import Data.Coerce (coerce)
import qualified Data.DList as DL
import Data.Function (on)
import Data.Kind (Constraint)
import Data.Membership
import Data.Ord (comparing)
import Data.Proxy
import GHC.Exts (Proxy#)
import GHC.Records
import GHC.TypeLits
import Type.Reflection (Typeable, typeRep)
import Unsafe.Coerce (unsafeCoerce)

data Dependency env is
  = DepRule (SomeMember is)
  | DepField !(SomeFieldOf env)
  | Global
  deriving (Eq, Ord)

instance AllKey Printable is => Show (Dependency env is) where
  showsPrec _ Global = showString "Global"
  showsPrec d (DepField (AField l)) =
    showParen (d > 10) $ showString "Field " . shows (symbolVal' l)
  showsPrec d (DepRule (SomeMembership (mem :: Membership i is))) =
    withMem @Printable mem $
      showParen (d > 10) $ showString "Rule " . strPrec 11 (Proxy @i)

type family AllKey' c ks :: Constraint where
  AllKey' _ '[] = ()
  AllKey' c ('(k, _) ': kvs) = (c k, AllKey c kvs)

class AllKey' c ks => AllKey c ks where
  withMem :: Membership i ks -> (c i => r) -> r

instance AllKey c '[] where
  withMem = \case

instance (AllKey c ks, c k) => AllKey c ('(k, v) ': ks) where
  withMem Here act = act
  withMem (There mem) act = withMem @c mem act

class Printable a where
  strPrec :: Int -> proxy a -> ShowS

instance Typeable a => Printable a where
  strPrec d = const $ showsPrec d $ typeRep @a

instance {-# OVERLAPPING #-} KnownSymbol l => Printable l where
  strPrec _ = showString . symbolVal

data SomeFieldOf a where
  AField :: (KnownSymbol l, HasField l a x) => Proxy# l -> SomeFieldOf a

fieldName :: SomeFieldOf a -> String
fieldName (AField sym#) = symbolVal' sym#

instance Show (SomeFieldOf a) where
  showsPrec d = showsPrec d . fieldName

instance Eq (SomeFieldOf a) where
  (==) = (==) `on` fieldName
  (/=) = (/=) `on` fieldName

instance Ord (SomeFieldOf a) where
  compare = comparing fieldName

newtype Offset j = Offset Int
  deriving newtype (Eq)

succO :: Offset j -> Offset (a ': j)
succO = coerce $ succ @Int

depGraph :: Build env '[] is a -> G.AdjacencyMap (Dependency env is)
depGraph = fst . depGraphWith (Offset @'[] 0)

depGraphWith ::
  Offset js ->
  Build env js is a ->
  (G.AdjacencyMap (Dependency env is), Offset is)
depGraphWith off IPure {} = (G.empty, off)
depGraphWith off (IAp l r) =
  let (g, off') = depGraphWith off l
      (h, off'') = depGraphWith off' r
   in (G.gmap (shift off' off'') g `G.overlay` h, off'')
depGraphWith off (IMap _ a) = depGraphWith off a
depGraphWith off (Rule (_ :: Proxy# l) act) =
  let src = G.vertex $ DepRule (SomeMembership $ membership @l)
      dst = G.vertices $ listRuleDeps act
   in (src `G.connect` dst, succO off)

shift :: Offset js1 -> Offset is -> Dependency env js1 -> Dependency env is
shift (Offset beg) (Offset end) dep =
  case dep of
    (DepRule mem) -> DepRule $ unsafeShift (end - beg) mem
    (DepField senv) -> DepField senv
    Global -> Global

unsafeShift :: Int -> SomeMember js1 -> SomeMember is
unsafeShift n (SomeMembership i)
  | n <= 0 = SomeMembership $ unsafeCoerce i
  | otherwise = unsafeShift (n - 1) $ SomeMembership $ There i

listRuleDeps :: Rule env is a -> [Dependency env ('(k, v) ': is)]
listRuleDeps = DL.toList . getConst . interpRuleA go

go :: RuleF env is x -> Const (DL.DList (Dependency env ('(k, v) ': is))) x
{-# INLINE go #-}
go f = case f of
  Depends (_ :: Proxy# l) ->
    Const $
      DL.singleton $
        DepRule (SomeMembership $ There $ membership @l)
  Whole -> Const $ DL.singleton Global
  (Field psl) ->
    Const $
      DL.singleton $
        DepField (AField psl)
