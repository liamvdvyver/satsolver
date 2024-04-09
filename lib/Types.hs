module Types where

-- Objects are just nullary functions
data Term = Function Identifier Int [Term] | Var String
    deriving (Show, Ord, Eq)

-- Propositional variables are just nullary predicates
-- We will reserve nullary predicates "T" and "F"
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
    | Universally Term Formula
    deriving (Show, Ord, Eq)

data Sequent = Entails [Formula] Formula
    deriving Show
