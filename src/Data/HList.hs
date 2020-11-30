{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeOperators #-}

module Data.HList where

import Data.Kind (Type)
import Data.Membership
import Unsafe.Coerce (unsafeCoerce)

-- N.B. If one takes efficiency seriously,
-- 'HList' should be newtyped @SmallArray Any@,
-- or at least be @Vector Any@.
-- Since the current stage is just a PoC,
-- we are currently using this /slow/ representation.
data HList h (as :: [(k, Type)]) where
  HNil :: HList h '[]
  (:-) :: forall l h a as. h l a -> HList h as -> HList h ('(l, a) ': as)

infixr 9 :-

-- If Membership is just a newtyped Int and HList a Vector/SmallArray,
-- it becomes just an constant indexing.
ix :: Membership k as -> HList h as -> h k (Lookup' k as)
ix (There rest) (_ :- xs) = unsafeCoerce $ ix rest xs
ix Here (hkv :- _) = hkv
