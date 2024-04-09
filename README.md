# SemAntic Tableaux solver

**(Not a SAT solver)**

Simple sequent checker, grammar and recursive descent parser for classical logic.

Predicate logic is currently being implemented, so lots of things don't work!

## Usage

e.g. `satsolve '!(x&y)|-!x|!y'`

## Grammar

Where usual precedence applies. See the module Parser for a precise
specification used for implementation.

## Todo

- [x] Parse predicate logic sequents
- [ ] BFS or iterative deepening
- [ ] Identify variables in a branch
- [ ] Identify free/bound variables
- [ ] Expand quantifiers
