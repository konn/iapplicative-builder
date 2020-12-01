{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}

module Data.Membership where

import GHC.TypeLits (ErrorMessage (..), TypeError)

type family Lookup l is where
  Lookup _ '[] = 'Nothing
  Lookup k ('(k, v) ': _) = 'Just v
  Lookup k (_ ': ks) = Lookup k ks

type Lookup' k kvs = FromJust k kvs (Lookup k kvs)

type Absent k kvs = Lookup k kvs ~ 'Nothing

type family FromJust k kvs m where
  FromJust _ _ ( 'Just v) = v
  FromJust k kvs _ =
    TypeError
      ( 'Text "A label `"
          ':<>: 'ShowType k
          ':<>: 'Text "' is absent in:"
          ':$$: 'Text "\t"
          ':<>: 'ShowType kvs
      )

-- N.B. If one takes efficiency seriously,
-- 'Membership' should be newtyped 'Int'.
-- Since the current situation is just a PoC,
-- we use this /slow/ representation here.
data Membership a as where
  Here :: Membership k ('(k, v) ': ks)
  There :: Membership k ks -> Membership k ('(k', v') ': ks)

deriving instance Show (Membership a as)

withMembership ::
  Membership a as -> (Member a as => r) -> r
{-# INLINE withMembership #-}
withMembership Here act = act
withMembership (There mem) act = withMembership mem act

class Member l ls where
  membership :: Membership l ls

instance {-# INCOHERENT #-} Member k ('(k, v) ': ks) where
  membership = Here
  {-# INLINE membership #-}

instance {-# INCOHERENT #-} Member k ks => Member k ('(k', v) ': ks) where
  membership = There $ membership @k @ks
  {-# INLINE membership #-}

data SomeMember ls where
  SomeMembership :: Membership l ls -> SomeMember ls

deriving instance Show (SomeMember as)

instance Eq (SomeMember ls) where
  (==) = \(SomeMembership l) (SomeMembership r) -> eqMembership l r
  (/=) = \(SomeMembership l) (SomeMembership r) -> neqMembership l r

instance Ord (SomeMember ls) where
  compare = \(SomeMembership l) (SomeMembership r) ->
    cmpMembership l r

neqMembership, eqMembership :: Membership l ls -> Membership l1 ls -> Bool
eqMembership Here {} There {} = False
eqMembership Here {} Here {} = True
eqMembership There {} Here {} = False
eqMembership (There l) (There r) = eqMembership l r
neqMembership Here {} There {} = True
neqMembership Here {} Here {} = False
neqMembership There {} Here {} = True
neqMembership (There l) (There r) = neqMembership l r

cmpMembership :: Membership l ls -> Membership l1 ls -> Ordering
cmpMembership Here {} Here {} = EQ
cmpMembership Here {} There {} = LT
cmpMembership There {} Here {} = GT
cmpMembership (There l) (There r) = cmpMembership l r
