
{-# LANGUAGE FlexibleInstances #-}
module Solver where

import Data.Char
import Data.List as List
import qualified Data.Set as Set
import Types

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
    substitute (Predication predicate terms) from to = Predication predicate $ map (\t -> substitute t from to) terms

instance Substitute Term where
    substitute term from to
        | term == from = to
        | otherwise = case term of
            Var s -> Var s
            FunctionApplication function terms' -> FunctionApplication function $ map (\t -> substitute t from to) terms'

class Free t where
    free :: t -> Set.Set Term

-- | Find free terms in formula
instance Free Formula where
    free (And a b) = free a `Set.union` free b
    free (Or a b) = free a `Set.union` free b
    free (Not a) = free a
    free (Implies a b) = free a `Set.union` free b
    free (Iff a b) = free a `Set.union` free b
    free (Existentially bound formula) = Set.filter (/= bound) $ free formula
    free (Universally bound formula _) = Set.filter (/= bound) $ free formula
    free (Predication _ t) = foldl' Set.union Set.empty $ map free t

instance Free Term where
    free v@(Var _) = Set.singleton v
    free f@(FunctionApplication _ ts) = f `Set.insert` foldl' Set.union Set.empty (map free ts)

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

-- -- | Find free terms in branch
-- instance Free NodeLabel where
--     free lns = lns >>= free

-- | Find functions in branch
branchFunctions :: NodeLabel -> Set.Set Function
branchFunctions lns = freeFuncs
  where
    freeTerms = Set.unions $ map free lns
    freeFuncs = Set.unions $ Set.map getFunction freeTerms
    getFunction :: Term -> Set.Set Function
    getFunction (FunctionApplication f _) = Set.singleton f
    getFunction _ = Set.empty

-- | Instantiate new object to branch
eigenVar :: NodeLabel -> Term
eigenVar lns = FunctionApplication (Function newName 0) []
  where
    candidates :: [String]
    candidates = [c ++ n | n <- "" : map show [1 :: Int ..], c <- map (pure . chr) [97 .. 122]]

    funcs :: Set.Set Function
    funcs = branchFunctions lns

    getFuncName :: Function -> Identifier
    getFuncName (Function ident _) = ident

    funcNames :: Set.Set Identifier
    funcNames = Set.map getFuncName funcs

    newName :: Identifier
    newName = head $ filter (\x -> not $ x `Set.member` funcNames) candidates

-- | Get the (multiples) lines (for multiple branches) which follow from a line of a proof
branchLine :: Signed -> NodeLabel -> Branches
branchLine line branch = map (map UnFinally) $ case line of
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
    -- Replace equivalent quantifiers
    (F (Existentially v a)) -> [[T (Universally v (Not a) Set.empty)]]
    (F (Universally v a _)) -> [[T (Existentially v (Not a))]]
    -- Instantiate object and substitute var in formula
    (T (Existentially v a)) -> [[T $ substitute a v newObj]]
      where
        newObj = eigenVar branch
    -- Add line for each object in the branch, and keep
    -- Then keep this here since we need to apply to later instantiated objects
    -- Branches can still close with this behaviour
    -- But in checking for openness, we just need to check that there are no
    -- further object to apply the rule to
    -- TODO: We will probably need to branch into a set
    (T (Universally v a applied)) -> [T (Universally v a (Set.union applied terms')) : fs]
      where
        terms = Set.unions (map free branch)
        terms' = if null terms then Set.singleton $ eigenVar branch else terms -- Add object if empty
        fs = Set.toList $ Set.map (T . substitute a v) terms'
    -- Non-simplifying proof lines
    (T _) -> error "Interpretation of predicate does not branch"
    (F _) -> error "Interpretation of predciate does not branch"

{- | Number of branches to be explored when expanding a Then
TODO:  Use this to branch as late as possible
-}
nBranches :: ProofStep -> NodeLabel -> Int
nBranches (Then _ branches) _ = length branches
nBranches (UnFinally line) branch = length $ branchLine line branch
nBranches _ _ = 1

-- | Turn an unFinally into a subproof, i.e. a list containing Finally or a Then (applying one step of simplification)
finalise :: ProofStep -> [ProofStep] -> ProofStep
finalise (UnFinally f@(T (Predication _ _))) _ = Finally f
finalise (UnFinally f@(F (Predication _ _))) _ = Finally f
finalise (UnFinally line) branch = Then line $ branchLine line branch
finalise x _ = x

-- | Get a tuple of (True Vars, False Vars)
getInterpretations :: NodeLabel -> Interpretations
getInterpretations proofNodes = (trues, falses)
  where
    isInterpretation :: ProofStep -> Bool
    isInterpretation (Finally (T (Predication _ _))) = True
    isInterpretation (Finally (F (Predication _ _))) = True
    isInterpretation _ = False

    fromFinally :: ProofStep -> Signed
    fromFinally (Finally a) = a
    fromFinally _ = error "Not Finally"

    isTrue :: Signed -> Bool
    isTrue (T _) = True
    isTrue (F _) = False

    fromSigned :: Signed -> Formula
    fromSigned (T a@(Predication _ _)) = a
    fromSigned (F a@(Predication _ _)) = a
    fromSigned ln = error $ "Not an interpretation" ++ pretty ln

    interpretations = map fromFinally $ filter isInterpretation proofNodes
    trueVars = Set.fromList $ map fromSigned $ filter isTrue interpretations
    falseVars = Set.fromList $ map fromSigned $ filter (not . isTrue) interpretations

    trues = Set.union trueVars $ Set.fromList [true]
    falses = Set.union falseVars $ Set.fromList [false]

-- | Check whether a branch is closed, based on assigned values
isClosed :: NodeLabel -> Bool
isClosed proofNodes = not $ Set.disjoint trues falses
  where
    (trues, falses) = getInterpretations proofNodes

-- | Check whether branch is open
isOpen :: NodeLabel -> Bool
isOpen proofNodes = not (isClosed proofNodes) && fullyExpanded proofNodes
  where
    fullyExpanded :: NodeLabel -> Bool
    fullyExpanded [] = True
    -- True universal expansion doesn't leave the branch
    -- So, check if we can apply the rule to any new objects
    fullyExpanded ((UnFinally (T (Universally _ _ ts))) : xs)
        | ts == Set.unions (map free proofNodes) = fullyExpanded xs
        | otherwise = False
    fullyExpanded ((UnFinally _) : _) = False
    fullyExpanded ((Then _ _) : _) = False
    fullyExpanded (_ : xs) = fullyExpanded xs

-- | Children for recursion by expanding thens
getChildren :: NodeLabel -> Branches
getChildren = combineThens [[]]
  where
    isThen (Then _ _) = True
    isThen _ = False

    fromThen :: ProofStep -> Branches
    fromThen (Then _ b) = b
    fromThen _ = error "Not a Then"

    -- Recursive helper
    combineThens :: Branches -> NodeLabel -> Branches
    combineThens acc [] = acc
    combineThens acc (x : xs)
        | isThen x = combineThens ([existing ++ new | existing <- acc, new <- fromThen x]) xs
        | otherwise = combineThens (map (++ [x]) acc) xs

-- | Recursively prove
prove :: Int -> NodeLabel -> ProofNode
prove depth xs
    | depth <= 0 = Proof xs Cutoff Nothing
    | isClosed proof = Proof xs Closed Nothing
    | isOpen proof = Proof xs (Open [interpretations]) Nothing
    | childIsOpen = Proof xs (Open mergedInterpretations) (Just provenChildren)
    | childrenAreClosed = Proof xs Closed (Just provenChildren)
    | otherwise = Proof xs Cutoff Nothing -- TODO: WHAT CASE IS THIS
  where
    proof = map (`finalise` xs) xs

    children = getChildren proof

    provenChildren = map (prove $ depth - 1) children

    isLiteralOpen :: ProofNode -> Bool
    isLiteralOpen (Proof _ (Open _) _) = True
    isLiteralOpen _ = False

    isLiteralClosed :: ProofNode -> Bool
    isLiteralClosed (Proof _ Closed _) = True
    isLiteralClosed _ = False

    openChildren = filter isLiteralOpen provenChildren
    childIsOpen = any isLiteralOpen provenChildren

    childrenAreClosed = all isLiteralClosed provenChildren

    interpretations = getInterpretations proof

    fromNode :: ProofNode -> [Interpretations]
    fromNode (Proof _ (Open a) _) = a
    fromNode _ = error "Not a singleton Open"

    openChildInterpretations = map fromNode openChildren
    mergedInterpretations = foldl List.union [] openChildInterpretations

-- | Setup a proof from a sequent
setupProof :: Sequent -> NodeLabel
setupProof (Entails a b) = UnFinally (F b) : [UnFinally (T x) | x <- a]

-- | Check if a sequent is valid
isValid :: Sequent -> Maybe Bool
isValid s = case proveSequent s of
    (Proof _ Closed _) -> Just True
    (Proof _ (Open _) _) -> Just False
    _ -> Nothing

idDfsProve :: Int -> Int -> NodeLabel -> ProofNode
idDfsProve depth maxDepth xs = case proven of
    (Proof _ Closed _) -> proven
    (Proof _ (Open _) _) -> proven
    _
        | depth >= maxDepth -> proven
        | otherwise -> idDfsProve (depth + 1) maxDepth xs
  where
    proven = prove depth xs

-- | Prove a sequent
proveSequent :: Sequent -> ProofNode
proveSequent = idDfsProve 1 99 . setupProof
