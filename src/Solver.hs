module Solver where

import qualified Data.Set as Set

-- Should be user-defined
data Var = P | Q | R | S | FromString String
    deriving (Show, Ord, Eq)

data Formula
    = FromVar Var
    | And Formula Formula
    | Or Formula Formula
    | Not Formula
    | Implies Formula Formula
    | Iff Formula Formula
    deriving (Show, Ord, Eq)

data ProofLine = T Formula | F Formula | Open | Closed
    deriving (Show, Eq)

data ProofNode
    = Then ProofLine Alternates -- A Line which branches to several sub-proofs
    | UnFinally ProofLine -- Line which still may branch
    | Finally ProofLine -- Line which is known not to branch
    deriving (Show, Eq)

{-
A proof is a [ProofNode]:
[ Finally $ T antedent
, F consequent `Then` [[    <- Then creates a sub-proof, where we can discard the consequent
    [[ Finally T a
    ,  UnFinally [T b]      <- This will become Finally T b if it does not branch
    ]]
]
-}
type Alternates = [Consecutives] -- Branched Possibilities
type Consecutives = [ProofNode]
type Interpretations = (Set.Set Var, Set.Set Var) -- (trues, falses)

{- | Get the (multiples) lines (for multiple branches) which follow from a line of a proof

Inner lists: consecutive lines in branch
Outer lists: seperate branches

>>> branchLine $ T (FromVar P `Iff` FromVar Q)
[[UnFinally (T (FromVar P)),UnFinally (T (FromVar Q))],[UnFinally (F (FromVar P)),UnFinally (F (FromVar Q))]]
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
    (F (Implies a b)) -> [[T a], [F b]]
    (T (Iff a b)) -> [[T a, T b], [F a, F b]]
    (F (Iff a b)) -> [[T a, F b], [F a, T b]]
    -- Non-simplifying proof lines
    Open -> error "Open does not branch"
    Closed -> error "Closed does not branch"
    (T _) -> error "Interpretation of variable does not branch"
    (F _) -> error "Interpretation of variable does not branch"

-- Sort unexpanded connectives on the basis of how many branches
--
--

{- | Turn an unFinally into a subproof, i.e. a list containing Finally or a Then (applying one step of simplification)

>>> finalise $ UnFinally (T (FromVar P))
Finally (T (FromVar P))
>>> finalise $ Finally (T (FromVar P))
Finally (T (FromVar P))
>>> finalise $ UnFinally (T (Or (FromVar P) (FromVar Q)))
Then (T (Or (FromVar P) (FromVar Q))) [[UnFinally (T (FromVar P))],[UnFinally (T (FromVar Q))]]
-}
finalise :: ProofNode -> ProofNode
finalise (UnFinally Open) = Finally Open
finalise (UnFinally Closed) = Finally Closed
finalise (UnFinally f@(T (FromVar _))) = Finally f
finalise (UnFinally f@(F (FromVar _))) = Finally f
finalise (UnFinally line) = Then line $ branchLine line
finalise x = x

{- | Get a tuple of (True Vars, False Vars)

>>> getInterpretations [Finally $ T (FromVar P), Finally $ F (FromVar P), Finally $ T (FromVar Q), Finally $ T (FromVar P `Or` FromVar Q), UnFinally $ T (FromVar Q)]
(fromList [P,Q],fromList [P])
-}
getInterpretations :: Consecutives -> Interpretations
getInterpretations proofNodes = (trues, falses)
  where
    isInterpretation :: ProofNode -> Bool
    isInterpretation (Finally (T (FromVar _))) = True
    isInterpretation (Finally (F (FromVar _))) = True
    isInterpretation _ = False

    fromFinally :: ProofNode -> ProofLine
    fromFinally (Finally a) = a
    fromFinally _ = error "Not Finally"

    isTrue :: ProofLine -> Bool
    isTrue (T _) = True
    isTrue (F _) = False
    isTrue _ = error "Not an interpretation"

    fromProofLine :: ProofLine -> Var
    fromProofLine (T (FromVar a)) = a
    fromProofLine (F (FromVar a)) = a
    fromProofLine _ = error "Not an interpretation"

    interpretations = map fromFinally $ filter isInterpretation proofNodes
    trues = Set.fromList $ map fromProofLine $ filter isTrue interpretations
    falses = Set.fromList $ map fromProofLine $ filter (not . isTrue) interpretations

{- | Check whether a branch is closed, based on assigned values

>>> isClosed [Finally $ T $ FromVar P, Finally $ F $ FromVar P]
True
>>> isClosed [Finally $ T $ FromVar P, UnFinally $ F $ FromVar P]
False
-}
isClosed :: Consecutives -> Bool
isClosed proofNodes = not $ Set.disjoint trues falses
  where
    (trues, falses) = getInterpretations proofNodes

{- Check whether branch is open

>>> isOpen [Finally $ T $ FromVar P, Finally F $ FromVar Q]
True
>>> isOpen [Finally $ T $ FromVar P, Finally F $ FromVar P]
False
>>> isOpen [Finally $ T $ FromVar P, Finally F $ FromVar Q, UnFinally ]
False
>>> isOpen [(Finally $ T $ (FromVar P)), Then (F $ (FromVar P) `Or` (FromVar Q)) [[(UnFinally $ F $ FromVar P), (UnFinally $ F $ FromVar Q)]]] -- The parent
False
>>> isOpen [(Finally $ T $ (FromVar P)), (UnFinally $ F $ FromVar P), (UnFinally $ F $ FromVar Q)]
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
nBranches :: ProofNode -> Int
nBranches (Then _ b) = length b
nBranches _ = 1

{- | Children for recursion

>>> getChildren [(Finally $ T $ (FromVar P)), Then (F $ (FromVar P) `Or` (FromVar Q)) [[(UnFinally $ F $ FromVar P), (UnFinally $ F $ FromVar Q)]]]
[[Finally (T (FromVar P)),UnFinally (F (FromVar P)),UnFinally (F (FromVar Q))]]
-}
getChildren :: Consecutives -> Alternates
getChildren proofNodes = map (\x -> finals ++ x ++ thens) (fromThen fstThen)
  where
    isFinal (Finally _) = True
    isFinal _ = False
    isThen (Then _ _) = True
    isThen _ = False

    finals = filter isFinal proofNodes

    allThens = filter isThen proofNodes
    (fstThen, thens) = case allThens of
        x : xs -> (x, xs)
        [] -> error "No further branching"

    fromThen :: ProofNode -> Alternates
    fromThen (Then _ b) = b
    fromThen _ = error "Not a Then"

{- | Recursively prove

>>> proofStep [(Finally $ T $ (FromVar P)), (UnFinally $ F $ (FromVar P) `And` (FromVar Q))]
[Finally Open]
>>> proofStep [(Finally $ T $ (FromVar P)), (Finally $ F $ FromVar P), (Finally $ F $ FromVar Q)]
[Finally Closed]
>>> proofStep [(Finally $ T $ (FromVar P)), (UnFinally $ F $ FromVar P), (UnFinally $ F $ FromVar Q)] -- The child
[Finally Closed]
>>> proofStep [(Finally $ T $ (FromVar P)), Then (F $ (FromVar P) `Or` (FromVar Q)) [[(UnFinally $ F $ FromVar P), (UnFinally $ F $ FromVar Q)]]] -- The parent
[Finally Closed]
>>> proofStep [(Finally $ T $ (FromVar P)), (UnFinally $ F $ (FromVar P) `Or` (FromVar Q))]
[Finally Closed]
-}
proofStep :: Consecutives -> Consecutives
proofStep xs
    | isClosed proof = [Finally Closed]
    | isOpen proof = [Finally Open]
    | [Finally Open] `elem` map proofStep children = [Finally Open]
    | not $ null unFinals = error "Checking proof outcome before finalising steps"
    | otherwise = [Finally Closed] -- Make sure we always hit this case, then clean up
  where
    proof = map finalise xs
    isUnFinal (UnFinally _) = True
    isUnFinal _ = False
    unFinals = filter isUnFinal proof
    children = getChildren proof

data Sequent = Entails Formula Formula

{- | Check if a sequent is valid

>>> isValid $ (Not $ (FromVar P) `Or` (FromVar Q)) `Entails` ((Not $ FromVar P) `And` (Not $ FromVar Q))
True
>>> isValid $ (((FromVar P) `Or` (FromVar Q)) `Iff` ((FromVar R) `Or` (FromVar S))) `Entails` (((FromVar P) `Iff` (FromVar R)) `Or` ((FromVar Q) `Iff` (FromVar S)))
False
-}
isValid :: Sequent -> Bool
isValid (Entails a b) = case proofStep proof of
    [Finally Open] -> False
    [Finally Closed] -> True
    _ -> error "Did not reduce"
  where
    proof =
        [ UnFinally (T a)
        , UnFinally (F b)
        ]
