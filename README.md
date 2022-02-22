# cqfd

**Cqfd** is a why3-certified automatic prover for propositional logic.

## Construction

The core algorithm is implemented and verified in **Why3** and takes the form of a collection of strategies which search for proofs. Strategies are all proven correct and can be extracted to **OCaml**.

## Features

+ Automatic proof of boolean formulas in a context

## WIP

+ Proof text extraction (in french)

## Ideas

+ Extension to first order logic ?
+ Fallback to *sat* if the prover fails ?

