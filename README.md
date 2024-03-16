# SemAntic Tableaux solver

**(Not a SAT solver)**

Simple sequent checker, grammar and recursive descent parser for propositional logic.

## Usage

## Grammar

Inputs to be parsed should be sequents of the form:

```
Sequent     ::= Formula ("," Formula)* "|-" Formula
Formula     ::= Negation | Binary | "(" Formula ")" | Atom
Negation    ::= "!" Formula
Binary      ::= Equivalence | Implication | Disjunction | Conjunction
Equivalence ::= Formula "=" Formula
Implication ::= Formula ">" Formula
Disjunction ::= Formula "|" Formula
Conjunction ::= Formula "&" Formula
Atom        ::= "T" | "F" | Identifier
Identifier  ::= CHAR
```

Where usual precedence applies. See the module Parser for a precise
specification used for implementation.

## Todo

* Iterative deepening.
* Support predicate logic.
