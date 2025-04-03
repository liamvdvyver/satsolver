# SemAntic Tableaux solver

**(Not a SAT solver)**

Semantic tableaux prover for first order logic.

_(Well, it is a SAT solver, but not the best tool for that job ...)_

## Usage

#### Examples:

- `satsolve '!(x&y)|-!x|!y'`
- `satsolve '|-Ex(F(x)->Vy(F(y)))'`

### Tips:

This can only check sequents for now, by attempting to find a countermodel.
To check for satisfiability, see if a set of premises must contradict.

#### Examples:

- `satsolve 'p,q|-F'`
- `satsolve 'p,!p|-F'`

## Grammar

A snippet from `Logic.Parser`:

```
{- The complete grammar:

Variable ::= Identifier
Function ::= Identifier "(" Function ("," Function)* ")" | Variable
Predicate ::= Identifier ("(" Function ("," Function)* ")")?
Grouping ::= "(" Formula ")" | Predicate
Negation ::= "!" Negation | Grouping
Quantification ::= ("E" | "V") Variable Quantification | Negation
Conjunction ::= Quantification ("&" Quantification)*
Disjunction ::= Conjunction ("|" Conjunction)*
Implication ::= Disjuntion ("->" Disjunction)*
Equivalence ::= Implication ("=" Implication)*
Formula ::= Equivalence
Sequent ::= Formula ("," Formula)* "|-" Formula

-}
```

With my apologies for presenting this in a recursive-descent-parser-readable rather than human-readable format!

## The details

To be developed, but for now, uses set-labelled tableaux without unification, searching depth-first with iterative deepening up to a depth of 99.
More control to come soon.
