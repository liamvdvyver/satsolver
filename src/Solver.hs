module Solver where

import Data.List as List
import qualified Data.Set as Set

-- Should be user-defined
-- TODO: Assign ConstTrue to be True immediately, etc
data Atom = Var Char | ConstTrue | ConstFalse
    deriving (Show, Ord, Eq)

data Formula
    = FromAtom Atom
    | And Formula Formula
    | Or Formula Formula
    | Not Formula
    | Implies Formula Formula
    | Iff Formula Formula
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
type Interpretations = (Set.Set Atom, Set.Set Atom) -- (trues, falses)

{- | Get the (multiples) lines (for multiple branches) which follow from a line of a proof

>>> branchLine $ T (FromAtom (Var 'P') `Iff` FromAtom (Var 'Q'))
[[UnFinally (T (FromAtom (Var 'P'))),UnFinally (T (FromAtom (Var 'Q')))],[UnFinally (F (FromAtom (Var 'P'))),UnFinally (F (FromAtom (Var 'Q')))]]
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
    (T _) -> error "Interpretation of variable does not branch"
    (F _) -> error "Interpretation of variable does not branch"

{- | Turn an unFinally into a subproof, i.e. a list containing Finally or a Then (applying one step of simplification)

>>> finalise $ UnFinally (T (FromAtom (Var 'P')))
Finally (T (FromAtom (Var 'P')))
>>> finalise $ Finally (T (FromAtom (Var 'P')))
Finally (T (FromAtom (Var 'P')))
>>> finalise $ UnFinally (T (Or (FromAtom (Var 'P')) (FromAtom (Var 'Q'))))
Then (T (Or (FromAtom (Var 'P')) (FromAtom (Var 'Q')))) [[UnFinally (T (FromAtom (Var 'P')))],[UnFinally (T (FromAtom (Var 'Q')))]]
-}
finalise :: ProofNode -> ProofNode
finalise (UnFinally f@(T (FromAtom _))) = Finally f
finalise (UnFinally f@(F (FromAtom _))) = Finally f
finalise (UnFinally line) = Then line $ branchLine line
finalise x = x

{- | Get a tuple of (True Vars, False Vars)

>>> getInterpretations [Finally $ T (FromAtom (Var 'P')), Finally $ F (FromAtom (Var 'P')), Finally $ T (FromAtom (Var 'Q')), Finally $ T (FromAtom (Var 'P') `Or` FromAtom (Var 'Q')), UnFinally $ T (FromAtom (Var 'Q'))]
(fromList [Var 'P',Var 'Q',ConstTrue],fromList [Var 'P',ConstFalse])
-}
getInterpretations :: Consecutives -> Interpretations
getInterpretations proofNodes = (trues, falses)
  where
    isInterpretation :: ProofNode -> Bool
    isInterpretation (Finally (T (FromAtom _))) = True
    isInterpretation (Finally (F (FromAtom _))) = True
    isInterpretation _ = False

    fromFinally :: ProofNode -> ProofLine
    fromFinally (Finally a) = a
    fromFinally _ = error "Not Finally"

    isTrue :: ProofLine -> Bool
    isTrue (T _) = True
    isTrue (F _) = False

    fromProofLine :: ProofLine -> Atom
    fromProofLine (T (FromAtom a)) = a
    fromProofLine (F (FromAtom a)) = a
    fromProofLine _ = error "Not an interpretation"

    interpretations = map fromFinally $ filter isInterpretation proofNodes
    trueVars = Set.fromList $ map fromProofLine $ filter isTrue interpretations
    falseVars = Set.fromList $ map fromProofLine $ filter (not . isTrue) interpretations

    trues = Set.union trueVars $ Set.fromList [ConstTrue]
    falses = Set.union falseVars $ Set.fromList [ConstFalse]

{- | Check whether a branch is closed, based on assigned values

>>> isClosed [Finally $ T $ FromAtom (Var 'P'), Finally $ F $ FromAtom (Var 'P')]
True
>>> isClosed [Finally $ T $ FromAtom (Var 'P'), UnFinally $ F $ FromAtom (Var 'P')]
False
-}
isClosed :: Consecutives -> Bool
isClosed proofNodes = not $ Set.disjoint trues falses
  where
    (trues, falses) = getInterpretations proofNodes

{- Check whether branch is open

>>> isOpen [Finally $ T $ FromAtom (Var 'P'), Finally F $ FromAtom (Var 'Q')]
True
>>> isOpen [Finally $ T $ FromAtom (Var 'P'), Finally F $ FromAtom (Var 'P')]
False
>>> isOpen [Finally $ T $ FromAtom (Var 'P'), Finally F $ FromAtom (Var 'Q'), UnFinally ]
False
>>> isOpen [(Finally $ T $ (FromAtom (Var 'P'))), Then (F $ (FromAtom (Var 'P')) `Or` (FromAtom (Var 'Q'))) [[(UnFinally $ F $ FromAtom (Var 'P')), (UnFinally $ F $ FromAtom (Var 'Q'))]]] -- The parent
False
>>> isOpen [(Finally $ T $ (FromAtom (Var 'P'))), (UnFinally $ F $ FromAtom (Var 'P')), (UnFinally $ F $ FromAtom (Var 'Q'))]
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

>>> getChildren [(Finally $ T $ (FromAtom (Var 'P'))), Then (F $ (FromAtom (Var 'P')) `Or` (FromAtom (Var 'Q'))) [[(UnFinally $ F $ FromAtom (Var 'P')), (UnFinally $ F $ FromAtom (Var 'Q'))]]]
[[Finally (T (FromAtom (Var 'P'))),UnFinally (F (FromAtom (Var 'P'))),UnFinally (F (FromAtom (Var 'Q')))]]
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

>>> prove [(Finally $ T $ (FromAtom (Var 'P'))), (UnFinally $ F $ (FromAtom (Var 'P')) `And` (FromAtom (Var 'Q')))]
[Open [(fromList [Var 'P',ConstTrue],fromList [Var 'Q',ConstFalse])]]
>>> prove [(Finally $ T $ (FromAtom (Var 'P'))), (Finally $ F $ FromAtom (Var 'P')), (Finally $ F $ FromAtom (Var 'Q'))]
[Closed]
>>> prove [(Finally $ T $ (FromAtom (Var 'P'))), (UnFinally $ F $ FromAtom (Var 'P')), (UnFinally $ F $ FromAtom (Var 'Q'))] -- The child
[Closed]
>>> prove [(Finally $ T $ (FromAtom (Var 'P'))), Then (F $ (FromAtom (Var 'P')) `Or` (FromAtom (Var 'Q'))) [[(UnFinally $ F $ FromAtom (Var 'P')), (UnFinally $ F $ FromAtom (Var 'Q'))]]] -- The parent
[Closed]
>>> prove [(Finally $ T $ (FromAtom (Var 'P'))), (UnFinally $ F $ (FromAtom (Var 'P')) `Or` (FromAtom (Var 'Q')))]
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

data Sequent = Entails Formula Formula
    deriving Show

-- | Setup a proof from a sequent
setupProof :: Sequent -> Consecutives
setupProof (Entails a b) = [UnFinally (T a), UnFinally (F b)]

{- | Check if a sequent is valid

>>> isValid $ (Not $ (FromAtom (Var 'P')) `Or` (FromAtom (Var 'Q'))) `Entails` ((Not $ FromAtom (Var 'P')) `And` (Not $ FromAtom (Var 'Q')))
True
>>> isValid $ (((FromAtom (Var 'P')) `Or` (FromAtom (Var 'Q'))) `Iff` ((FromAtom (Var 'R')) `Or` (FromAtom (Var 'S')))) `Entails` (((FromAtom (Var 'P')) `Iff` (FromAtom (Var 'R'))) `Or` ((FromAtom (Var 'Q')) `Iff` (FromAtom (Var 'S'))))
False
-}
isValid :: Sequent -> Bool
isValid s = case proveSequent s of
    [Open _] -> False
    [Closed] -> True
    _ -> error "Did not reduce"

-- | Prove a sequent
--
-- >>> proveSequent $ (((FromAtom (Var 'P')) `Or` (FromAtom (Var 'Q'))) `Iff` ((FromAtom (Var 'R')) `Or` (FromAtom (Var 'S')))) `Entails` (((FromAtom (Var 'P')) `Iff` (FromAtom (Var 'R'))) `Or` ((FromAtom (Var 'Q')) `Iff` (FromAtom (Var 'S'))))
-- [Open [(fromList [Var 'P',Var 'S',ConstTrue],fromList [Var 'Q',Var 'R',ConstFalse]),(fromList [Var 'Q',Var 'R',ConstTrue],fromList [Var 'P',Var 'S',ConstFalse])]]
proveSequent :: Sequent -> Consecutives
proveSequent = prove . setupProof
