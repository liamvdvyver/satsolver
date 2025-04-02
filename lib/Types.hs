module Types where

import qualified Data.Set as Set

data Term = FunctionApplication Function [Term] | Var String
    deriving (Show, Ord, Eq)

data Function = Function Identifier Int
    deriving (Show, Ord, Eq)

-- Objects are just nullary functions
obj :: Identifier -> Term
obj s = FunctionApplication (Function s 0) []

data Predicate = Predicate Identifier Int
    deriving (Show, Ord, Eq)

data Equality = Equality Term Term

type Identifier = String

data Formula
    = And Formula Formula
    | Or Formula Formula
    | Not Formula
    | Implies Formula Formula
    | Iff Formula Formula
    | Predication Predicate [Term]
    | Existentially Term Formula
    | Universally Term Formula (Set.Set Term) -- Keep track of which objects the rule has been applied to
    deriving (Show, Ord, Eq)

-- Propositional variables are just nullary predicates
prop :: Identifier -> Formula
prop v = Predication (Predicate v 0) []

-- We will reserve nullary predicates "T" and "F"
true :: Formula
true = prop "T"

false :: Formula
false = prop "F"

data Sequent = Entails [Formula] Formula
    deriving (Show, Eq)
