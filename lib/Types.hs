{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE UndecidableInstances #-}
module Types where

import qualified Data.Set as Set

class Pretty t where
    pretty :: t -> String

instance Pretty String where
    pretty = id

commaSeparate :: (Pretty t) => [t] -> String
commaSeparate [] = ""
commaSeparate (x : xs) = pretty x ++ foldl (\a b -> a ++ "," ++ commaSeparate xs) "" xs

inBrackets :: (Pretty t) => t -> String
inBrackets x = case str of
    "" -> str
    (_ : _) -> "(" ++ str ++ ")"
  where
    str = pretty x

data Term = FunctionApplication Function [Term] | Var String
    deriving (Show, Ord, Eq)

instance Pretty Term where
    pretty (FunctionApplication f t) = pretty f ++ (inBrackets . commaSeparate) t
    pretty (Var s) = s


data Function = Function Identifier Int
    deriving (Show, Ord, Eq)

instance Pretty Function where
    pretty (Function ident _) = ident

-- Objects are just nullary functions
obj :: Identifier -> Term
obj s = FunctionApplication (Function s 0) []

data Predicate = Predicate Identifier Int
    deriving (Show, Ord, Eq)

instance Pretty Predicate where
    pretty (Predicate identifier _) = identifier

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

instance Pretty Formula where
    pretty (p `And` q) = pretty p ++ "∧" ++ pretty q
    pretty (p `Or` q) = pretty p ++ "∨" ++ pretty q
    pretty (Not p) = "¬" ++ pretty p
    pretty (p `Implies` q) = pretty p ++ "→" ++ pretty q
    pretty (p `Iff` q) = pretty p ++ "↔" ++ pretty q
    pretty (Predication predicate terms) = pretty predicate ++ (inBrackets $ commaSeparate terms)
    pretty (Existentially t f) = "∃" ++ pretty t ++ (inBrackets . pretty) f
    pretty (Universally t f _) = "∀" ++ pretty t ++ (inBrackets . pretty) f

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

instance Pretty Sequent where
    pretty (x `Entails` y) = commaSeparate x ++ "|-" ++ pretty y

data Signed = T Formula | F Formula
    deriving (Show, Eq, Ord)

instance Pretty Signed where
    pretty (T f) = "T: " ++ pretty f
    pretty (F f) = "F: " ++ pretty f

data ProofStep
    = Then Signed Branches -- A line, with the (branched) subformulae it red
    | UnFinally Signed -- Line which has not been expanded to its subformulae yet
    | Finally Signed -- Line which is known not to branch
    | Open [Interpretations] -- Keep track of variable assignment to find counterexample
    | Closed
    | Cutoff
    deriving (Show, Eq)

prettyInts :: [Interpretations] -> String
prettyInts i = commaSeparate (map pretty' i) where
            pretty' (ts, fs) = "(" ++  prettyTs ++ ", " ++ prettyFs ++ ")"
                where
                    prettyTs = commaSeparate $ Set.toList $ Set.map (("T: " ++) . pretty) ts
                    prettyFs = commaSeparate $ Set.toList $ Set.map (("F: " ++) . pretty) fs

instance Pretty ProofStep where
    pretty (Finally s) = pretty s
    pretty (UnFinally s) = "(" ++ pretty s ++ ")"
    pretty (Then s b) = "(" ++ pretty s ++ ")" ++ " (branch) "
    pretty (Open i) = "Model :" ++ prettyInts i
    pretty Closed = "Closed"
    pretty Cutoff = "(Cutoff)"

type Branches = [NodeLabel] -- Branched Possibilities
type NodeLabel = [ProofStep]
type Interpretations = (Set.Set Formula, Set.Set Formula) -- (trues, falses)

data ProofNode = Proof NodeLabel ProofStep (Maybe [ProofNode])
    deriving Eq

instance Pretty ProofNode where
    pretty (Proof label _ children) = unlines $ labelText : childrenText
        where
            labelText = unlines $ map pretty label
            indent = "    "
            childrenText :: [String]
            childrenText = map (indent ++) $ concatMap lines $ case children of
                Nothing -> []
                Just c -> map pretty c

