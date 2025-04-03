module Logic where

import qualified Data.Set as Set

data Term = ApplyFunc {func :: Function, funcArgs :: [Term]} | Var {unVar :: Identifier}
    deriving (Show, Ord, Eq)

data Function = Function {funcSymbol :: Identifier, funcArity :: Int}
    deriving (Show, Ord, Eq)

-- Objects are just nullary functions
obj :: Identifier -> Term
obj s = ApplyFunc (Function s 0) []

data Predicate = Predicate {predSymbol :: Identifier, predArity :: Int}
    deriving (Show, Ord, Eq)

data Equality = Equality Term Term

type Identifier = String

data Formula
    = And {left :: Formula, right :: Formula}
    | Or {left :: Formula, right :: Formula}
    | Not {unNot :: Formula}
    | Implies {antecedent :: Formula, consequent :: Formula}
    | Iff {left :: Formula, right :: Formula}
    | ApplyPred {pred :: Predicate, predArgs :: [Term]}
    | Existentially {bound :: Term, quantified :: Formula}
    | Universally {bound :: Term, quantified :: Formula, applied :: Set.Set Term} -- Keep track of which objects the rule has been applied to
    deriving (Show, Ord, Eq)

-- Propositional variables are just nullary predicates
prop :: Identifier -> Formula
prop v = ApplyPred (Predicate v 0) []

-- We will reserve nullary predicates "T" and "F"
true :: Formula
true = prop "T"

false :: Formula
false = prop "F"

data Sequent = Entails [Formula] Formula
    deriving (Show, Eq)

class Substitute t where
    substitute :: t -> Term -> Term -> t

instance Substitute Formula where
    substitute (And f g) from to = And (substitute f from to) (substitute g from to)
    substitute (Or f g) from to = Or (substitute f from to) (substitute g from to)
    substitute (Not f) from to = Not (substitute f from to)
    substitute (Implies f g) from to = Implies (substitute f from to) (substitute g from to)
    substitute (Iff f g) from to = Iff (substitute f from to) (substitute g from to)
    substitute q@(Existentially v f) from to
        | v == from = q
        | otherwise = Existentially v (substitute f from to)
    substitute q@(Universally v f t) from to
        | v == from = q
        | otherwise = Universally v (substitute f from to) t
    substitute (ApplyPred predicate terms) from to = ApplyPred predicate $ map (\t -> substitute t from to) terms

instance Substitute Term where
    substitute term from to
        | term == from = to
        | otherwise = case term of
            Var s -> Var s
            ApplyFunc function terms' -> ApplyFunc function $ map (\t -> substitute t from to) terms'

class Free t where
    free :: t -> Set.Set Term

-- | Find free terms in formula
instance Free Formula where
    free (And a b) = free a `Set.union` free b
    free (Or a b) = free a `Set.union` free b
    free (Not a) = free a
    free (Implies a b) = free a `Set.union` free b
    free (Iff a b) = free a `Set.union` free b
    free (Existentially b q) = Set.filter (/= b) $ free q
    free (Universally b q _) = Set.filter (/= b) $ free q
    free (ApplyPred _ t) = Set.unions $ map free t

instance Free Term where
    free v@(Var _) = Set.singleton v
    free f@(ApplyFunc _ ts) = f `Set.insert` Set.unions (map free ts)
