{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}

module Data.Functor.Indexed.WrapCategory where

import Control.Category (Category)
import qualified Control.Category as Cat
import Data.Coerce
import Data.Functor.Contravariant
import Data.Functor.Indexed

-- | Turns a 'Category' into 'IxApplicative', adjoining a phantom return types.
newtype WrapCategory arr i j a = WrapCategory {runCategory :: arr i j}
  deriving (Functor)

instance Contravariant (WrapCategory arr i j) where
  contramap = const coerce
  {-# INLINE contramap #-}

instance IxFunctor (WrapCategory arr) where
  imap = const coerce
  {-# INLINE imap #-}

instance Category arr => IxPointed (WrapCategory arr) where
  ireturn = const $ WrapCategory Cat.id
  {-# INLINE ireturn #-}

instance Category arr => IxApplicative (WrapCategory arr) where
  {-# INLINE iap #-}
  iap =
    coerce $ (Cat.>>>) @arr @i @j @k ::
      forall i j k a b.
      WrapCategory arr i j (a -> b) ->
      WrapCategory arr j k a ->
      WrapCategory arr i k b
