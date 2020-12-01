{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}

module Data.HList where

import Data.Membership
import Data.Proxy (Proxy (Proxy))
import Data.Type.Equality
import Unsafe.Coerce (unsafeCoerce)

-- N.B. If one takes efficiency seriously,
-- 'HList' should be newtyped @SmallArray Any@,
-- or at least be @Vector Any@.
-- Since the current stage is just a PoC,
-- we are currently using this /slow/ representation.
data HList h (as :: [(k, v)]) where
  HNil :: HList h '[]
  (:-) :: forall l h a as. h l a -> HList h as -> HList h ('(l, a) ': as)

infixr 9 :-

-- If Membership is just a newtyped Int and HList a Vector/SmallArray,
-- it becomes just an constant indexing.
ix :: Membership k as -> HList h as -> h k (Lookup' k as)
{-# INLINE ix #-}
ix (There rest) (_ :- xs) = unsafeCoerce $ ix rest xs
ix Here (hkv :- _) = hkv

mapHList :: (forall x t. h t x -> k t x) -> HList h xs -> HList k xs
{-# INLINE mapHList #-}
mapHList f hl = case hl of
  HNil -> HNil
  x :- xs -> f x :- mapHList f xs

class Generate xs where
  generateA ::
    forall h f.
    Applicative f =>
    ( forall k v proxy proxy'.
      Lookup k xs ~ 'Just v =>
      proxy k ->
      proxy' v ->
      f (h k v)
    ) ->
    f (HList h xs)

instance Generate '[] where
  generateA = \_ -> pure HNil
  {-# INLINE generateA #-}

instance
  ( Lookup k xs ~ 'Nothing
  , Generate xs
  ) =>
  Generate ('(k, v) ': xs)
  where
  {-# INLINE generateA #-}
  generateA = \f ->
    (:-) <$> f (Proxy @k) (Proxy @v) <*> generateA do
      \(k' :: proxy k') (v' :: proxy' v') ->
        gcastWith
          (unsafeCoerce $ Refl @() :: Lookup k' ('(k, v) ': xs) :~: 'Just v')
          $ f k' v'
