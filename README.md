# SemAntic Tableaux solver

**(Not a SAT solver)**

Simple sequent checker, grammar and recursive descent parser for classical logic.

Predicate logic is currently being implemented, so lots of things don't work!

## Usage

Examples:

- `satsolve '!(x&y)|-!x|!y'`
- `satsolve '|-Ex(F(x)->Vy(F(y)))'`

## Grammar

Where usual precedence applies. See the module Parser for a precise
specification used for implementation.

## Todo

- [ ] Iterative deepening
