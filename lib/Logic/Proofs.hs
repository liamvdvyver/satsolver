module Logic.Proofs where

import Logic

import qualified Data.Set as Set
import qualified Data.List as List

data Signed = T {unSigned :: Formula} | F {unSigned :: Formula}
    deriving (Show, Eq, Ord)

data Line
    = Then Signed Branched -- A line, with the (branched) subformulae it red
    | UnFinally Signed -- Line which has not been expanded to its subformulae yet
    | Finally Signed -- Line which is known not to branch
    deriving (Show, Eq)

data ProofValue
    = Open [Model] -- Keep track of variable assignment to find counterexample
    | Closed
    | Cutoff
    deriving (Show, Eq)

newtype Branched = Branched {unBranched :: [LineSet]} -- Branched Possibilities
    deriving (Show, Eq)

newtype LineSet = LineSet {unLineSet :: [Line]}
    deriving (Show, Eq)

data Model = Model
    { trues :: Set.Set Formula
    , falses :: Set.Set Formula
    }
    deriving (Show, Eq)

-- data ProofNode = Proof NodeLabel ProofStep (Maybe [ProofNode])
data ProofNode = Proof
    { curLines :: LineSet
    , expandedLines :: LineSet
    , nodeValue :: ProofValue
    , children :: Maybe [ProofNode]
    }
    deriving (Eq)

-- | Get lines still to be expanded, plus lines already expanded
allLines :: ProofNode -> LineSet
allLines node = LineSet $ List.nub $ unLineSet (curLines node) ++ unLineSet (expandedLines node)

instance Free Line where
    free (Finally (T formula)) = free formula
    free (Finally (F formula)) = free formula
    free (UnFinally (T formula)) = free formula
    free (UnFinally (F formula)) = free formula
    free (Then (T formula) _) = free formula
    free (Then (F formula) _) = free formula

instance Free LineSet where
    free = Set.unions . map free . unLineSet
