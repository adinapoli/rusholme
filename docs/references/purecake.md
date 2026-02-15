# PureCake: A Verified Compiler for a Lazy Functional Language

> Source: PLDI 2023
> Authors: Hrutvik Kanabar, Samuel Vivien, Oskar Abrahamsson, Magnus O. Myreen,
>          Michael Norrish, Johannes Åman Pohjola, Riccardo Zanetti
> Retrieved: 2026-02-15

## Summary

PureCake is a mechanically-verified compiler for PureLang, a lazy, purely
functional programming language inspired by Haskell. It targets CakeML as its
backend, offering end-to-end correctness for compilation down to machine code.
Developed entirely within the HOL4 interactive theorem prover.

## Key Features

- Haskell-like, indentation-sensitive source language (PureLang)
- Constraint-based Hindley-Milner type system
- Sound equational reasoning principles
- Verified demand analysis
- Verified optimizations for lazy idioms and monadic reflection
- First verified end-to-end result for any lazy language

## Relevance to Rusholme

Interesting for correctness guarantees and as a reference for how to compile
lazy evaluation, but targeting CakeML limits backend flexibility. Less directly
applicable to our multi-backend goals than GRIN.

## Links

- Project: https://cakeml.org/purecake
- Paper: Available via ACM Digital Library (PLDI 2023)
