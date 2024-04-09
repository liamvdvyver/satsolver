module Solver where

import Data.List as List
import qualified Data.Set as Set

-- Objects are just nullary functions
data Term = Function String Int [Term] | Var String
    deriving (Show, Ord, Eq)

-- Propositional variables are just nullary predicates
-- We will reserve nullary predicates "T" and "F"
data Predicate = Predicate String Int [Term]
    deriving (Show, Ord, Eq)

data Equality = Equality Term Term

data Formula
    = FromPredicate Predicate
    | And Formula Formula
    | Or Formula Formula
    | Not Formula
    | Implies Formula Formula
    | Iff Formula Formula
    | Predication Predicate [Term]
    deriving (Show, Ord, Eq)

data ProofLine = T Formula | F Formula
    deriving (Show, Eq)

data ProofNode
    = Then ProofLine Alternates -- A Line which branches to several sub-proofs
    | UnFinally ProofLine -- Line which still may branch
    | Finally ProofLine -- Line which is known not to branch
    | Open [Interpretations] -- Keep track of variable assignment to find counterexample
    | Closed
    deriving (Show, Eq)

type Alternates = [Consecutives] -- Branched Possibilities
type Consecutives = [ProofNode]
type Interpretations = (Set.Set Predicate, Set.Set Predicate) -- (trues, falses)

{- | Get the (multiples) lines (for multiple branches) which follow from a line of a proof

>>> branchLine $ T (FromPredicate (Predicate "P" 0 []) `Iff` FromPredicate (Predicate "Q" 0 []))
[[UnFinally (T (FromPredicate (Predicate "P" 0 []))),UnFinally (T (FromPredicate (Predicate "Q" 0 [])))],[UnFinally (F (FromPredicate (Predicate "P" 0 []))),UnFinally (F (FromPredicate (Predicate "Q" 0 [])))]]
-}
branchLine :: ProofLine -> Alternates
branchLine line = map (map UnFinally) $ case line of
    (T (Not a)) -> [[F a]]
    (F (Not a)) -> [[T a]]
    (T (And a b)) -> [[T a, T b]]
    (F (And a b)) -> [[F a], [F b]]
    (T (Or a b)) -> [[T a], [T b]]
    (F (Or a b)) -> [[F a, F b]]
    (T (Implies a b)) -> [[F a], [T a, T b]]
    (F (Implies a b)) -> [[T a, F b]]
    (T (Iff a b)) -> [[T a, T b], [F a, F b]]
    (F (Iff a b)) -> [[T a, F b], [F a, T b]]
    -- Non-simplifying proof lines
    (T _) -> error "Interpretation of variable does not branch"
    (F _) -> error "Interpretation of variable does not branch"

{- | Turn an unFinally into a subproof, i.e. a list containing Finally or a Then (applying one step of simplification)

>>> finalise $ UnFinally (T (FromPredicate (Predicate "P" 0 [])))
Finally (T (FromPredicate (Predicate "P" 0 [])))
>>> finalise $ Finally (T (FromPredicate (Predicate "P" 0 [])))
Finally (T (FromPredicate (Predicate "P" 0 [])))
>>> finalise $ UnFinally (T (Or (FromPredicate (Predicate "P" 0 [])) (FromPredicate (Predicate "Q" 0 []))))
Then (T (Or (FromPredicate (Predicate "P" 0 [])) (FromPredicate (Predicate "Q" 0 [])))) [[UnFinally (T (FromPredicate (Predicate "P" 0 [])))],[UnFinally (T (FromPredicate (Predicate "Q" 0 [])))]]
-}
finalise :: ProofNode -> ProofNode
finalise (UnFinally f@(T (FromPredicate _))) = Finally f
finalise (UnFinally f@(F (FromPredicate _))) = Finally f
finalise (UnFinally line) = Then line $ branchLine line
finalise x = x

{- | Get a tuple of (True Vars, False Vars)

>>> getInterpretations [Finally $ T (FromPredicate (Predicate "P" 0 [])), Finally $ F (FromPredicate (Predicate "P" 0 [])), Finally $ T (FromPredicate (Predicate "Q" 0 [])), Finally $ T (FromPredicate (Predicate "P" 0 []) `Or` FromPredicate (Predicate "Q" 0 [])), UnFinally $ T (FromPredicate (Predicate "Q" 0 []))]
(fromList [Predicate "P" 0 [],Predicate "Q" 0 [],Predicate "T" 0 []],fromList [Predicate "F" 0 [],Predicate "P" 0 []])
-}
getInterpretations :: Consecutives -> Interpretations
getInterpretations proofNodes = (trues, falses)
  where
    isInterpretation :: ProofNode -> Bool
    isInterpretation (Finally (T (FromPredicate _))) = True
    isInterpretation (Finally (F _)) = True
    isInterpretation _ = False

    fromFinally :: ProofNode -> ProofLine
    fromFinally (Finally a) = a
    fromFinally _ = error "Not Finally"

    isTrue :: ProofLine -> Bool
    isTrue (T _) = True
    isTrue (F _) = False

    fromProofLine :: ProofLine -> Predicate
    fromProofLine (T (FromPredicate a)) = a
    fromProofLine (F (FromPredicate a)) = a
    fromProofLine _ = error "Not an interpretation"

    interpretations = map fromFinally $ filter isInterpretation proofNodes
    trueVars = Set.fromList $ map fromProofLine $ filter isTrue interpretations
    falseVars = Set.fromList $ map fromProofLine $ filter (not . isTrue) interpretations

    trues = Set.union trueVars $ Set.fromList [Predicate "T" 0 []]
    falses = Set.union falseVars $ Set.fromList [Predicate "F" 0 []]

{- | Check whether a branch is closed, based on assigned values

>>> isClosed [Finally $ T $ FromPredicate (Predicate "P" 0 []), Finally $ F $ FromPredicate (Predicate "P" 0 [])]
True
>>> isClosed [Finally $ T $ FromPredicate (Predicate "P" 0 []), UnFinally $ F $ FromPredicate (Predicate "P" 0 [])]
False
-}
isClosed :: Consecutives -> Bool
isClosed proofNodes = not $ Set.disjoint trues falses
  where
    (trues, falses) = getInterpretations proofNodes

{- Check whether branch is open

>>> isOpen [Finally $ T $ FromPredicate (Predicate "P" 0 []), Finally F $ FromPredicate (Predicate "Q" 0 [])]
True
>>> isOpen [Finally $ T $ FromPredicate (Predicate "P" 0 []), Finally F $ FromPredicate (Predicate "P" 0 [])]
False
>>> isOpen [Finally $ T $ FromPredicate (Predicate "P" 0 []), Finally F $ FromPredicate (Predicate "Q" 0 []), UnFinally ]
False
>>> isOpen [(Finally $ T $ (FromPredicate (Predicate "P" 0 []))), Then (F $ (FromPredicate (Predicate "P" 0 [])) `Or` (FromPredicate (Predicate "Q" 0 []))) [[(UnFinally $ F $ FromPredicate (Predicate "P" 0 [])), (UnFinally $ F $ FromPredicate (Predicate "Q" 0 []))]]] -- The parent
False
>>> isOpen [(Finally $ T $ (FromPredicate (Predicate "P" 0 []))), (UnFinally $ F $ FromPredicate (Predicate "P" 0 [])), (UnFinally $ F $ FromPredicate (Predicate "Q" 0 []))]
False
-}
isOpen :: Consecutives -> Bool
isOpen proofNodes = not (isClosed proofNodes) && fullyExpanded proofNodes
  where
    fullyExpanded :: Consecutives -> Bool
    fullyExpanded [] = True
    fullyExpanded ((UnFinally _) : _) = False
    fullyExpanded ((Then _ _) : _) = False
    fullyExpanded (_ : xs) = fullyExpanded xs

-- | Number of branches to be explored when expanding a Then
-- TODO:  Use this to branch as late as possible
nBranches :: ProofNode -> Int
nBranches (Then _ b) = length b
nBranches _ = 1

{- | Children for recursion

>>> getChildren [(Finally $ T $ (FromPredicate (Predicate "P" 0 []))), Then (F $ (FromPredicate (Predicate "P" 0 [])) `Or` (FromPredicate (Predicate "Q" 0 []))) [[(UnFinally $ F $ FromPredicate (Predicate "P" 0 [])), (UnFinally $ F $ FromPredicate (Predicate "Q" 0 []))]]]
[[Finally (T (FromPredicate (Predicate "P" 0 []))),UnFinally (F (FromPredicate (Predicate "P" 0 []))),UnFinally (F (FromPredicate (Predicate "Q" 0 [])))]]
-}
getChildren :: Consecutives -> Alternates
getChildren proofNodes = map (\x -> finals ++ x ++ tailThens) (fromThen headThen)
  where
    isFinal (Finally _) = True
    isFinal _ = False
    isThen (Then _ _) = True
    isThen _ = False

    finals = filter isFinal proofNodes

    thens = filter isThen proofNodes
    (headThen, tailThens) = case thens of
        x : xs -> (x, xs)
        [] -> error "No further branching"

    fromThen :: ProofNode -> Alternates
    fromThen (Then _ b) = b
    fromThen _ = error "Not a Then"

{- | Recursively prove

>>> prove [(Finally $ T $ (FromPredicate (Predicate "P" 0 []))), (UnFinally $ F $ (FromPredicate (Predicate "P" 0 [])) `And` (FromPredicate (Predicate "Q" 0 [])))]
[Open [(fromList [Predicate "P" 0 [],Predicate "T" 0 []],fromList [Predicate "F" 0 [],Predicate "Q" 0 []])]]
>>> prove [(Finally $ T $ (FromPredicate (Predicate "P" 0 []))), (Finally $ F $ FromPredicate (Predicate "P" 0 [])), (Finally $ F $ FromPredicate (Predicate "Q" 0 []))]
[Closed]
>>> prove [(Finally $ T $ (FromPredicate (Predicate "P" 0 []))), (UnFinally $ F $ FromPredicate (Predicate "P" 0 [])), (UnFinally $ F $ FromPredicate (Predicate "Q" 0 []))] -- The child
[Closed]
>>> prove [(Finally $ T $ (FromPredicate (Predicate "P" 0 []))), Then (F $ (FromPredicate (Predicate "P" 0 [])) `Or` (FromPredicate (Predicate "Q" 0 []))) [[(UnFinally $ F $ FromPredicate (Predicate "P" 0 [])), (UnFinally $ F $ FromPredicate (Predicate "Q" 0 []))]]] -- The parent
[Closed]
>>> prove [(Finally $ T $ (FromPredicate (Predicate "P" 0 []))), (UnFinally $ F $ (FromPredicate (Predicate "P" 0 [])) `Or` (FromPredicate (Predicate "Q" 0 [])))]
[Closed]
-}
prove :: Consecutives -> Consecutives
prove xs
    | isClosed proof = pure Closed
    | isOpen proof = pure $ Open [interpretations]
    | childIsOpen = pure $ Open mergedInterpretations
    | otherwise = pure Closed
  where
    proof = map finalise xs

    children = getChildren proof

    provenChildren = map prove children

    isLiteralOpen [Open _] = True
    isLiteralOpen _ = False
    openChildren = filter isLiteralOpen provenChildren
    childIsOpen = any isLiteralOpen provenChildren

    interpretations = getInterpretations proof
    fromNode [Open a] = a
    fromNode _ = error "Not a singleton Open"

    openChildInterpretations = map fromNode openChildren
    mergedInterpretations = foldl List.union [] openChildInterpretations

data Sequent = Entails [Formula] Formula
    deriving Show

-- | Setup a proof from a sequent
setupProof :: Sequent -> Consecutives
setupProof (Entails a b) = UnFinally (F b) : [UnFinally (T x)| x <- a]

{- | Check if a sequent is valid

>>> isValid $ [(Not $ (FromPredicate (Predicate "P" 0 [])) `Or` (FromPredicate (Predicate "Q" 0 [])))] `Entails` ((Not $ FromPredicate (Predicate "P" 0 [])) `And` (Not $ FromPredicate (Predicate "Q" 0 [])))
True
>>> isValid $ [(((FromPredicate (Predicate "P" 0 [])) `Or` (FromPredicate (Predicate "Q" 0 []))) `Iff` ((FromPredicate (Predicate "R" 0 [])) `Or` (FromPredicate (Predicate "S" 0 []))))] `Entails` (((FromPredicate (Predicate "P" 0 [])) `Iff` (FromPredicate (Predicate "R" 0 []))) `Or` ((FromPredicate (Predicate "Q" 0 [])) `Iff` (FromPredicate (Predicate "S" 0 []))))
False
-}
isValid :: Sequent -> Bool
isValid s = case proveSequent s of
    [Open _] -> False
    [Closed] -> True
    _ -> error "Did not reduce"

-- | Prove a sequent
--
-- >>> proveSequent $ [(((FromPredicate (Predicate "P" 0 [])) `Or` (FromPredicate (Predicate "Q" 0 []))) `Iff` ((FromPredicate (Predicate "R" 0 [])) `Or` (FromPredicate (Predicate "S" 0 []))))] `Entails` (((FromPredicate (Predicate "P" 0 [])) `Iff` (FromPredicate (Predicate "R" 0 []))) `Or` ((FromPredicate (Predicate "Q" 0 [])) `Iff` (FromPredicate (Predicate "S" 0 []))))
-- [Open [(fromList [Predicate "P" 0 [],Predicate "S" 0 [],Predicate "T" 0 []],fromList [Predicate "F" 0 [],Predicate "Q" 0 [],Predicate "R" 0 []]),(fromList [Predicate "Q" 0 [],Predicate "R" 0 [],Predicate "T" 0 []],fromList [Predicate "F" 0 [],Predicate "P" 0 [],Predicate "S" 0 []])]]
proveSequent :: Sequent -> Consecutives
proveSequent = prove . setupProof
