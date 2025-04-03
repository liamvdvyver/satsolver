module Logic.Solver where

import Logic
import Logic.Pretty
import Logic.Proofs

import Data.Char
import qualified Data.Set as Set

-- | Find functions in branch
branchFunctions :: NodeLabel -> Set.Set Function
branchFunctions (Node lns) = freeFuncs
  where
    freeTerms = Set.unions $ map free lns
    freeFuncs = Set.unions $ Set.map getFunction freeTerms
    getFunction :: Term -> Set.Set Function
    getFunction (FunctionApplication f _) = Set.singleton f
    getFunction _ = Set.empty

-- | Instantiate new object to branch
eigenVar :: NodeLabel -> Term
eigenVar node = FunctionApplication (Function newName 0) []
  where
    candidates :: [String]
    candidates = [c ++ n | n <- "" : map show [1 :: Int ..], c <- map (pure . chr) [97 .. 122]]

    funcs :: Set.Set Function
    funcs = branchFunctions node

    getFuncName :: Function -> Identifier
    getFuncName (Function ident _) = ident

    funcNames :: Set.Set Identifier
    funcNames = Set.map getFuncName funcs

    newName :: Identifier
    newName = head $ filter (\x -> not $ x `Set.member` funcNames) candidates

-- | Get the (multiples) lines (for multiple branches) which follow from a line of a proof
branchLine :: Signed -> NodeLabel -> Branches
branchLine line branch = Branches $ map (Node . map UnFinally) $ case line of
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
        terms = free branch
        terms' = if null terms then Set.singleton $ eigenVar branch else terms -- Add object if empty
        fs = Set.toList $ Set.map (T . substitute a v) terms'
    -- Non-simplifying proof lines
    (T _) -> error "Interpretation of predicate does not branch"
    (F _) -> error "Interpretation of predciate does not branch"

{- | Number of branches to be explored when expanding a Then
TODO:  Use this to branch as late as possible
-}
nBranches :: ProofStep -> NodeLabel -> Int
nBranches (Then _ (Branches branches)) _ = length branches
nBranches (UnFinally line) branch = length res
  where
    (Branches res) = branchLine line branch
nBranches _ _ = 1

-- | Turn an unFinally into a subproof, i.e. a list containing Finally or a Then (applying one step of simplification)
finalise :: ProofStep -> NodeLabel -> ProofStep
finalise (UnFinally f@(T (Predication _ _))) _ = Finally f
finalise (UnFinally f@(F (Predication _ _))) _ = Finally f
finalise (UnFinally line) branch = Then line $ branchLine line branch
finalise x _ = x

-- | Get a tuple of (True Vars, False Vars)
getInterpretations :: NodeLabel -> Interpretations
getInterpretations (Node lns) = Interpretations trues falses
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

    interpretations = map fromFinally $ filter isInterpretation lns
    trueVars = Set.fromList $ map fromSigned $ filter isTrue interpretations
    falseVars = Set.fromList $ map fromSigned $ filter (not . isTrue) interpretations

    trues = Set.union trueVars $ Set.fromList [true]
    falses = Set.union falseVars $ Set.fromList [false]

-- | Check whether a branch is closed, based on assigned values
isClosed :: NodeLabel -> Bool
isClosed proofNodes = not $ Set.disjoint trues falses
  where
    Interpretations trues falses = getInterpretations proofNodes

-- | Check whether branch is open
isOpen :: NodeLabel -> Bool
isOpen label@(Node lns) = not (isClosed label) && fullyExpanded lns
  where
    fullyExpanded :: [ProofStep] -> Bool
    fullyExpanded [] = True
    -- True universal expansion doesn't leave the branch
    -- So, check if we can apply the rule to any new objects
    fullyExpanded ((UnFinally (T (Universally _ _ ts))) : xs)
        | ts == free label = fullyExpanded xs
        | otherwise = False
    fullyExpanded ((UnFinally _) : _) = False
    fullyExpanded ((Then _ _) : _) = False
    fullyExpanded (_ : xs) = fullyExpanded xs

-- | Children for recursion by expanding thens
getChildren :: NodeLabel -> Branches
getChildren (Node lns) = Branches (map Node nestedSteps)
  where
    nestedSteps = combineThens [[]] lns

    isThen (Then _ _) = True
    isThen _ = False

    fromThen :: ProofStep -> [[ProofStep]]
    fromThen (Then _ (Branches b)) = [b' | (Node b') <- b]
    fromThen _ = error "Not a Then"

    -- Recursive helper
    combineThens :: [[ProofStep]] -> [ProofStep] -> [[ProofStep]]
    combineThens acc [] = acc
    combineThens acc (x : xs)
        | isThen x = combineThens ([existing ++ new | existing <- acc, new <- fromThen x]) xs
        | otherwise = combineThens (map (++ [x]) acc) xs

-- | Recursively prove
prove :: Int -> NodeLabel -> ProofNode
prove depth label@(Node xs)
    | depth <= 0 = Proof label Cutoff Nothing
    | isClosed proof = Proof label Closed Nothing
    | isOpen proof = Proof label (Open [interpretations]) Nothing
    | childIsOpen = Proof label (Open openChildInterpretations) (Just provenChildren)
    | childrenAreClosed = Proof label Closed (Just provenChildren)
    | otherwise = Proof label Cutoff Nothing -- TODO: WHAT CASE IS THIS
  where
    proof :: NodeLabel
    proof = Node [step `finalise` label | step <- xs]

    (Branches children) = getChildren proof

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

    openChildInterpretations = concatMap fromNode openChildren
    -- mergedInterpretations =
    --     foldl
    --         (\(Interpretations t f) (Interpretations t' f') -> Interpretations (t `Set.union` t') (f `Set.union` f'))
    --         (Interpretations Set.empty Set.empty)
    --         openChildInterpretations

-- | Setup a proof from a sequent
setupProof :: Sequent -> NodeLabel
setupProof (Entails a b) = Node $ UnFinally (F b) : [UnFinally (T x) | x <- a]

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
