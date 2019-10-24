# Zar

An experimental probabilistic programming language (PPL)

## Prereqs

* GHC 8.6.4

### Optional

To use the Z3 backend (disabled at the moment), build and install: https://github.com/Z3Prover/z3/tree/z3-4.8.1.

## Quickstart

```
stack build && stack exec zar-exe programs/fair_coin.zar
```
### Example

As an example of a Zar program, consider the following loop that simulates a fair coin from a biased one:

```
#File: programs/fair_coin.zar
main:
  p <- 1/3 #p can be any Rational in (0, 1)
  x <- false
  y <- false
  while x = y:
    x <~ bernoulli(p)
    y <~ bernoulli(p)
  return x
```

One can run this program by doing

```
> stack exec zar-exe programs/fair_coin.zar 
```

from the root of the repository.

Zar's surface syntax makes a distinction between a functional expression language and a conventional imperative probabilistic command language. For example, the following expressions over basic datatypes like lists are currently definable: 

```
func head (l : [int]) -> int :
  destruct(l, (0-1), \x:int. \xs:[int]. x)

func tail (l : [int]) -> [int] :
  destruct(l, []:int, \x:int. \xs:[int]. xs)

func concat (l1 : [int], l2 : [int]) -> [int] :
  destruct(l1, l2, \x:int. \xs:[int]. x :: concat(xs, l2))

func reverse (l : [int]) -> [int] :
  destruct(l, []:[int], \x:int. \xs:[int]. concat(reverse(xs), [x]:[int]))

func range (n : int) -> [int] :
  if n <= 0 then [] : [int] else concat(range(n-1), [n-1]:[int])
  
...
```

and can be used in the context of probabilistic commands such as: 

```
x <~ uniform(range(10))
```

As an alternative frontend, Zar can be used like an embedded DSL in Haskell (cf. `programs/Controller.hs` for an example).

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
