{-# LANGUAGE ApplicativeDo #-}
{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE OverloadedLabels #-}
{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeApplications #-}
{-# OPTIONS_GHC -Wno-partial-type-signatures #-}
{-# OPTIONS_GHC -dsuppress-idinfo -dsuppress-coercions -dsuppress-type-applications
-dsuppress-module-prefixes -dsuppress-type-signatures -dsuppress-uniques #-}

module Data.Builder.Applicative.IndexedSpec where

import Data.Builder.Applicative.Indexed
import Data.Builder.Applicative.Indexed.Types (RuleF)
import Data.Functor.Indexed
import Data.Proxy
import GHC.Base (inline)
import Test.Inspection
import Test.Tasty
import Test.Tasty.HUnit

data Input1 = Input1 {intVal :: Int, strVal :: String}
  deriving (Read, Show, Eq, Ord)

data Output1 = Output1 {intShown :: String, intStrVal :: String, constant :: Int}
  deriving (Read, Show, Eq, Ord)

-- Since the postcondition @js@ could be determined statically
-- once the precondition has been given, and they can change
-- if one adds new rule, you can use @PartialTypeSignatures@
-- to let such postconditions to be inferred.
--
-- We also use BlockArguments to save parens.
plan1 :: Build Input1 '[] _ ()
{-# INLINE plan1 #-}
plan1 =
  #rawIntVal
    (field @"intVal")
    *>> #rawStrVal (field @"strVal")
    *>> #shownIntVal do
      show <$> depends @"rawIntVal"
    *>> #appendedVal do
      (++) <$> depends @"shownIntVal" <*> depends @"rawStrVal"
    *>> #constVal do
      42 <$ depends @"shownIntVal"
    *>> #theOutput do
      intShown <- depends @"shownIntVal"
      constant <- depends @"constVal"
      intStrVal <- depends @"appendedVal"
      pure Output1 {..}

mkOutput1 :: Input1 -> Output1
{-# INLINE mkOutput1 #-}
mkOutput1 = inline build (Proxy @"theOutput") plan1

{-# INLINE output1 #-}
output1 :: Output1
output1 = mkOutput1 $ Input1 42 "foo"

test_concrete_fun :: TestTree
test_concrete_fun =
  testGroup
    "concrete builder doesn't include intermediate data types"
    [ testCase "No Build type" $
        case $(inspectTest $ 'mkOutput1 `hasNoType` ''Build) of
          Failure msg -> assertFailure msg
          Success {} -> pure ()
    , testCase "No Rule type" $
        case $(inspectTest $ 'mkOutput1 `hasNoType` ''Rule) of
          Failure msg -> assertFailure msg
          Success {} -> pure ()
    , testCase "No RuleF type" $
        case $(inspectTest $ 'mkOutput1 `hasNoType` ''RuleF) of
          Failure msg -> assertFailure msg
          Success {} -> pure ()
    ]

test_concrete_val :: TestTree
test_concrete_val =
  testGroup
    "fully applied value gets inlined"
    [ testCase "No Build type" $
        case $(inspectTest $ 'output1 `hasNoType` ''Build) of
          Failure msg -> assertFailure msg
          Success {} -> pure ()
    , testCase "No Rule type" $
        case $(inspectTest $ 'output1 `hasNoType` ''Rule) of
          Failure msg -> assertFailure msg
          Success {} -> pure ()
    , testCase "No RuleF type" $
        case $(inspectTest $ 'output1 `hasNoType` ''RuleF) of
          Failure msg -> assertFailure msg
          Success {} -> pure ()
    ]
