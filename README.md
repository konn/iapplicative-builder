# iapplicative-builder
Exploring indexed applicative style for statically typed build system for data with static and acyclic dependency.

## Abstract

Mokhov, Mitchel and Peyton Jones [gave a classification of various build systems][Build systems a la Carte] in terms of functorial constraints.
In particular, build systems using `Applicative` constraints are identified with a build system for *statically determined* dependency graphs.

However, their formulation based on (rank 1) functors cannot exclude *cyclic dependencies* statically, even though they explicitly exclude treatment of cyclic dependencies from their scopes.
In particular, their formulation uses concrete values for the key of each rule, and it potentially allows users to accidentally write rules involving cyclic dependencies.

In this repo, we try to extend their approach to statically exclude such cyclic dependencies, utilising both `Applicative` and *indexed* `Applicative` functors.

## Introduction
Our formulation involves two types: the applicative functor `Rule env is` and the indexed applicative functor `Build env is js`.
Intuitively:

- `Build env is js ()`: defines build rules with targets `js` from the predefined rules in `is` and the global environment `env`.
- `Rule env is a`: gives a concrete recipe for build a value `a` from the predefined rules available in `is` (excluding the rule being defined!) and the global environment `env`.

## Examples

See `app/Main.hs` for more example.

```hs
{-# LANGUAGE ApplicativeDo #-}
{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE TypeApplications #-}
plan1 :: Build Input1 '[] _ ()
plan1 =
  rule
    (Proxy @RawIntVal)
    (field @"intVal")
    *>> rule (Proxy @RawStrVal) (field @"strVal")
    *>> rule (Proxy @ShownIntVal) do
      show <$> depends @RawIntVal
    {-
    -- Uncommenting the following will result in a type error,
    -- which avoids duplication of the same rule:

    *>> rule (Proxy @RawStrVal) do
      pure "bad"
    -}
    *>> rule (Proxy @AppendedVal) do
      (++) <$> depends @ShownIntVal <*> depends @RawStrVal
    {-
    -- The following is also rejected since it mentions not-yet
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
```

With `-XQualifiedDo` and `-XOverloadeLabels`:

```hs
plan1' :: Build Input1 ('[] :: [(Symbol, Type)]) _ ()
plan1' = Ix.do
  #rawIntVal $ field @"intVal"
  #rawStrVal $ field @"strVal"
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
```

We can dump dependency graph from rules:

```haskell
ghci> depGraph plan1
edges [(Rule 'TheOutput,Rule 'ConstVal),(Rule 'TheOutput,Rule 'AppendedVal),(Rule 'TheOutput,Rule 'ShownIntVal),(Rule 'ConstVal,Rule 'ShownIntVal),(Rule 'AppendedVal,Rule 'ShownIntVal),(Rule 'AppendedVal,Rule 'RawStrVal),(Rule 'ShownIntVal,Rule 'RawIntVal),(Rule 'RawStrVal,Field "strVal"),(Rule 'RawIntVal,Field "intVal")]
```

## Thoughts
* We can make `Build` just an arrow; their return value is superfluous for now.
* Allow `Build`s to lift underlying applicative functors, like monad transformer.
* Optimised and/or cached builder utilising dependency graph information.
* Optimise `HList` and `Memberships` (we have battle-tested implementations of these, but haven't published yet...)

## References
* A. Mokhov, N. Mitchel, and S. Peyton Jones: [Build systems a la Carte].

[Build systems a la Carte]: https://www.microsoft.com/en-us/research/uploads/prod/2018/03/build-systems.pdf
