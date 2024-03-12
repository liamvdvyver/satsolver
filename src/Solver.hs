module Solver where

data (Eq a) => Atom a = Variable a
data Formula a
    = AsFormula (Atom a)
    | And (Formula a) (Formula a)
    | Or (Formula a) (Formula a)
    | Not (Formula a)
    | Implies (Formula a) (Formula a)
    | Iff (Formula a) (Formula a)

data ProofLine a = T (Formula a) | F (Formula a) | Open | Closed

data ProofNode a
    = Then (ProofLine a) [ProofNode a] -- Branches which follow from a line
    | UnFinally [ProofLine a] -- Branches which follow, and are yet to be explored
    | Finally (ProofLine a) -- Terminal line of a branch

simplifyLine :: ProofLine a -> [ProofNode a]
simplifyLine line = map UnFinally $ case line of
    (T (Not a)) -> [[F a]]
    (F (Not a)) -> [[T a]]
    (T (And a b)) -> [[T a, T b]]
    (F (And a b)) -> [[F a], [F b]]
    (T (Or a b)) -> [[T a], [T b]]
    (F (Or a b)) -> [[F a, F b]]
    (T (Implies a b)) -> [[F a], [T a, T b]]
    (F (Implies a b)) -> [[T a], [F b]]
    (T (Iff a b)) -> [[F a, T b], [F a, F b]]
    (F (Iff a b)) -> [[F a, T b], [T a, F b]]

    -- These shouldn't be used?
    a -> [[a]]
