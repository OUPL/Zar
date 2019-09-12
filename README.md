# Zar

An experimental probabilistic programming language (PPL)

## Prereqs

* GHC 8.6.4

### Optional

To use the Z3 backend (disabled at the moment), build and install: https://github.com/Z3Prover/z3/tree/z3-4.8.1.

## Quickstart

```
stack build && stack exec zar-exe programs/test1.ky
```

## Directory Structure

### app/

| File | What it does |
|------|--------------|
| Main.hs | The main entry point. Contains some code for generating random trees as well as reading and parsing programs |

### src/

| File | What it does |
|------|--------------|
| Datatypes.hs | Generic set-up for open recursion style data types |
| Tree.hs      | The tree functor, the type of well-founded trees and operations on them |
| ListTree.hs  | List representation of trees and operations on them, e.g., converting to and from the standard representation |
| Nat.hs       | Open recursion natural numbers |
| Cotree.hs    | Potentially infinite trees as the greatest fixed point of the tree functor |
| Sample.hs    | State-monad sampling of Cotrees |
| Inference.hs | Approximate inference via sampling |
| Sexp.hs      | Typeclass for serializing to s-expression format (e.g., in order to visualize trees using https://bagnalla.github.io/sexp-trees/) |
| Symtab.hs    | Symbol tables |
| Util.hs      | Miscellaneous utility functions including debug print |
| Lang.hs      | Abstract syntax (using GADTs and existential packages in the state); interpretation of commands as tree transformers |
| Distributions.hs | Primitive distributions (Uniform, Bernoulli, etc.) |
| Untyped.hs   | Untyped ASTs (typechecked and elaborated to the GADT representation) |
| Token.hs     | Parser-related stuff |
| Parser.hs    | Megaparsec parser |
| Tycheck.hs   | Typechecking / elaboration from untyped to GADT |

### programs/

| File | What it does |
|------|--------------|
| test.zar      | Simple example program |
| bernoulli.zar | Tests the built-in Bernoulli distribution |
| fair_coin.ky  | Simulates a fair coin using an unfair one |
| flips.ky      | A stochastic domination example from Justin Hsu's thesis |
| tricky_coin.ky| Tricky coin Bayesian inference |
