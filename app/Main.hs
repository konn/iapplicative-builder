{-# LANGUAGE ApplicativeDo #-}
{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE OverloadedLabels #-}
{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE TypeApplications #-}
{-# OPTIONS_GHC -Wno-partial-type-signatures #-}

module Main where

import Data.Builder.Applicative.Indexed
import Data.Builder.Applicative.Indexed.Dependency
import Data.Functor.Indexed
import Data.Kind
import Data.Proxy
import GHC.TypeLits (Symbol)

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
plan1 =
  rule
    (Proxy @RawIntVal)
    (field @"intVal")
    *>> rule (Proxy @RawStrVal) (field @"strVal")
    *>> rule (Proxy @ShownIntVal) do
      show <$> depends @RawIntVal
    {-
    -- Uncommenting the following will result in type error,
    -- which avoids duplication of the same rule:

    *>> rule (Proxy @RawStrVal) do
      pure "bad"
    -}
    *>> rule (Proxy @AppendedVal) do
      (++) <$> depends @ShownIntVal <*> depends @RawStrVal
    {-
    -- The following is also rejected, since it mentions not-yet
    -- defined rule ConstVal and AppendedVal itself:
    (++) <$> (show <$> depends @ConstVal) <*> depends @AppendedVal
    -}
    *>> rule (Proxy @ConstVal) do
      42 <$ depends @ShownIntVal
    *>> rule (Proxy @TheOutput) do
      intShown <- depends @ShownIntVal
      constant <- depends @ConstVal
      intStrVal <- depends @AppendedVal
      pure Output1 {..}

mkOutput1 :: Input1 -> Output1
mkOutput1 = build (Proxy @TheOutput) plan1

-- >>> mkOutput1 $ Input1 12 "foo"
-- Output1 {intShown = "12", intStrVal = "12foo", constant = 42}

-- * Same (isomorphic) rule using type-level symbols

-- We can use #foo notation (enabled by -XOverloadedLabels)
-- to define rules tagged with type level symbols!
plan1' :: Build Input1 ('[] :: [(Symbol, Type)]) _ ()
plan1' =
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

{- If we can use QualifiedDo extension, the above becomes:

plan1' :: Build Input1 ('[] :: [(Symbol, Type)]) _ ()
plan1' = Ix.do
  #rawIntVal $ field @"intVal"
  #rawStrVal $ field @"strVal")
  #shownIntVal do
    show <$> depends @"rawIntVal"
  #appendedVal do
    (++) <$> depends @"shownIntVal" <*> depends @"rawStrVal"
  #constVal do
    42 <$ depends @"shownIntVal"
  #theOutput do
    intShown <- depends @"shownIntVal"
    constant <- depends @"constVal"
    intStrVal <- depends @"appendedVal"
    pure Output1 {..}
-}

-- >>> depGraph plan1
-- edges [(Rule 'TheOutput,Rule 'ConstVal),(Rule 'TheOutput,Rule 'AppendedVal),(Rule 'TheOutput,Rule 'ShownIntVal),(Rule 'ConstVal,Rule 'ShownIntVal),(Rule 'AppendedVal,Rule 'ShownIntVal),(Rule 'AppendedVal,Rule 'RawStrVal),(Rule 'ShownIntVal,Rule 'RawIntVal),(Rule 'RawStrVal,Field "strVal"),(Rule 'RawIntVal,Field "intVal")]

main :: IO ()
main = do
  print $ mkOutput1 $ Input1 12 "foo"
  print $ build' @"theOutput" plan1' $ Input1 12 "foo"
  print $ depGraph plan1

data Targets1
  = RawIntVal
  | RawStrVal
  | ShownIntVal
  | AppendedVal
  | ConstVal
  | TheOutput
  deriving (Read, Show, Eq, Ord)

type RawIntVal = 'RawIntVal

type RawStrVal = 'RawStrVal

type ShownIntVal = 'ShownIntVal

type ConstVal = 'ConstVal

type AppendedVal = 'AppendedVal

type TheOutput = 'TheOutput
