# Lambda the Ultimate SSA: Optimizing Functional Programs in SSA

> Source: https://arxiv.org/abs/2201.07272
> Authors: Siddharth Bhat, Tobias Grosser
> Date: January 2022
> Retrieved: 2026-02-15

## Abstract

Static Single Assignment (SSA) is the workhorse of modern optimizing compilers
for imperative programming languages. However, functional languages have been
slow to adopt SSA and prefer to use intermediate representations based on
minimal lambda calculi due to SSA's inability to express higher order
constructs. We exploit a new SSA construct — regions — in order to express
functional optimizations via classical SSA based reasoning. Region optimization
currently relies on ad-hoc analyses and transformations on imperative programs.
These ad-hoc transformations are sufficient for imperative languages as regions
are used in a limited fashion. In contrast, we use regions pervasively to model
sub-expressions in our functional IR. This motivates us to systematize region
optimizations. We extend classical SSA reasoning to regions for functional-style
analyses and transformations. We implement a new SSA+regions based backend for
LEAN4, a theorem prover that implements a purely functional, dependently typed
programming language. Our backend is feature-complete and handles all constructs
of LEAN4's functional intermediate representation λrc within the SSA framework.
We evaluate our proposed region optimizations by optimizing λrc within an
SSA+regions based framework implemented in MLIR and demonstrating performance
parity with the current LEAN4 backend. We believe our work will pave the way
for a unified optimization framework capable of representing, analyzing, and
optimizing both functional and imperative languages.

## Relevance to Rusholme

This paper is relevant as a potential future direction if we want to explore
SSA-based optimisation within the GRIN pipeline. The key insight is that MLIR
regions can model functional sub-expressions, bridging the gap between SSA
(imperative) and lambda calculus (functional) intermediate representations.

## Links

- PDF: https://arxiv.org/pdf/2201.07272
- DOI: https://doi.org/10.48550/arXiv.2201.07272
