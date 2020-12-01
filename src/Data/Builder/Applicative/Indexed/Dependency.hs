{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE EmptyCase #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
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

depGraph :: Build env '[] is a -> G.AdjacencyMap (Dependency env is)
depGraph = fst . depGraphWith Stay

shiftDep :: Step is js -> Dependency env is -> Dependency env js
shiftDep off dep = case dep of
  DepRule (SomeMembership mem) ->
    DepRule $ SomeMembership $ walk off mem
  DepField senv -> DepField senv
  Global -> Global

depGraphWith ::
  Step is ks ->
  Build env js is a ->
  (G.AdjacencyMap (Dependency env ks), Step js is)
depGraphWith _ IPure {} = (G.empty, Stay)
depGraphWith off (IAp l r) =
  let (h, off') = depGraphWith off r
      (g, off'') = depGraphWith off' l
   in (G.gmap (shiftDep off) g `G.overlay` h, trans off'' off')
depGraphWith off (IMap _ a) = depGraphWith off a
depGraphWith off (Rule (_ :: Proxy# l) act) =
  let src = G.vertex $ DepRule (SomeMembership $ membership @l)
      dst = G.vertices $ listRuleDeps act
      grp = src `G.connect` dst
   in (G.gmap (shiftDep off) grp, Forward Stay)

data Step is js where
  Stay :: Step is is
  Forward :: Step is js -> Step is ('(k, v) ': js)

walk :: Step is js -> Membership l is -> Membership l js
walk Stay mem = mem
walk (Forward stp) mem = There $ walk stp mem

trans :: Step is js -> Step js ks -> Step is ks
trans l Stay = l
trans l (Forward r) = Forward $ trans l r

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
