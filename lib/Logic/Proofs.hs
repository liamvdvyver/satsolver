module Logic.Proofs where

import Logic

import qualified Data.Set as Set

data Signed = T Formula | F Formula
    deriving (Show, Eq, Ord)

data ProofStep
    = Then Signed Branches -- A line, with the (branched) subformulae it red
    | UnFinally Signed -- Line which has not been expanded to its subformulae yet
    | Finally Signed -- Line which is known not to branch
    | Open [Interpretations] -- Keep track of variable assignment to find counterexample
    | Closed
    | Cutoff
    deriving (Show, Eq)

newtype Branches = Branches [NodeLabel] -- Branched Possibilities
    deriving (Show, Eq)

newtype NodeLabel = Node [ProofStep]
    deriving (Show, Eq)

data Interpretations = Interpretations (Set.Set Formula) (Set.Set Formula) -- (trues, falses)
    deriving (Show, Eq)

data ProofNode = Proof NodeLabel ProofStep (Maybe [ProofNode])
    deriving (Eq)

instance Free ProofStep where
    free (Finally (T formula)) = free formula
    free (Finally (F formula)) = free formula
    free (UnFinally (T formula)) = free formula
    free (UnFinally (F formula)) = free formula
    free (Then (T formula) _) = free formula
    free (Then (F formula) _) = free formula
    free Closed = Set.empty
    free (Open _) = Set.empty
    free Cutoff = Set.empty

instance Free NodeLabel where
    free (Node steps) = Set.unions $ map free steps
