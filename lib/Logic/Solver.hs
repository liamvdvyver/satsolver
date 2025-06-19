module Logic.Solver where

import Logic
import Logic.Pretty
import Logic.Proofs

import Data.Char
import qualified Data.Set as Set
import qualified Data.List as List

-- | Find functions in branch
functions :: LineSet -> Set.Set Function
functions ls = freeFuncs
  where
    freeTerms = free ls
    freeFuncs = Set.unions $ Set.map getFunction freeTerms
    getFunction :: Term -> Set.Set Function
    getFunction (ApplyFunc f _) = Set.singleton f
    getFunction _ = Set.empty

-- | Instantiate new object to branch
eigenVar :: LineSet -> Term
eigenVar ls = ApplyFunc (Function newName 0) []
  where
    candidates :: [String]
    candidates = [c ++ n | n <- "" : map show [1 :: Int ..], c <- map (pure . chr) [97 .. 122]]

    funcs :: Set.Set Function
    funcs = functions ls

    getFuncName :: Function -> Identifier
    getFuncName (Function ident _) = ident

    funcNames :: Set.Set Identifier
    funcNames = Set.map getFuncName funcs

    newName :: Identifier
    newName = head $ filter (\x -> not $ x `Set.member` funcNames) candidates

-- | Get the (multiples) lines (for multiple branches) which follow from a line of a proof
branchLine :: Signed -> LineSet -> Branched
branchLine line branch = Branched $ map (LineSet . map UnFinally) $ case line of
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
    (T (Existentially v a)) -> [[T $ substitute a v (eigenVar branch)]]
    -- Add line for each object in the branch, and keep
    -- Then keep this here since we need to apply to later instantiated objects
    -- Branched can still close with this behaviour
    -- But in checking for openness, we just need to check that there are no
    -- further object to apply the rule to
    -- TODO: We will probably need to branch into a set
    (T (Universally b q a)) -> [T (Universally b q (Set.union a terms')) : fs]
      where
        terms = free branch
        terms' = if null terms then Set.singleton $ eigenVar branch else terms -- Add object if empty
        fs = Set.toList $ Set.map (T . substitute q b) terms'
    -- Non-simplifying proof lines
    (T _) -> error "Interpretation of predicate does not branch"
    (F _) -> error "Interpretation of predciate does not branch"

{- | Number of branches to be explored when expanding a Then
TODO:  Use this to branch as late as possible
-}
nBranched :: Line -> LineSet -> Int
nBranched (Then _ (Branched branches)) _ = length branches
nBranched (UnFinally line) branch = length res
  where
    (Branched res) = branchLine line branch
nBranched _ _ = 1

-- | Turn an unFinally into a subproof, i.e. a list containing Finally or a Then (applying one step of simplification)
finalise :: Line -> LineSet -> Line
finalise (UnFinally f@(T (ApplyPred _ _))) _ = Finally f
finalise (UnFinally f@(F (ApplyPred _ _))) _ = Finally f
finalise (UnFinally line) branch = Then line $ branchLine line branch
finalise x _ = x

-- | Get a tuple of (True Vars, False Vars)
getInterpretations :: LineSet -> Model
getInterpretations (LineSet lns) = Model allTrues allFalses
  where
    isInterpretation :: Line -> Bool
    isInterpretation (Finally (T (ApplyPred _ _))) = True
    isInterpretation (Finally (F (ApplyPred _ _))) = True
    isInterpretation _ = False

    fromFinally :: Line -> Signed
    fromFinally (Finally a) = a
    fromFinally _ = error "Not Finally"

    isTrue :: Signed -> Bool
    isTrue (T _) = True
    isTrue (F _) = False

    fromSigned :: Signed -> Formula
    fromSigned (T a@(ApplyPred _ _)) = a
    fromSigned (F a@(ApplyPred _ _)) = a
    fromSigned ln = error $ "Not an interpretation" ++ pretty ln

    interpretations = map fromFinally $ filter isInterpretation lns

    trueVars = Set.fromList $ map fromSigned $ filter isTrue interpretations
    falseVars = Set.fromList $ map fromSigned $ filter (not . isTrue) interpretations

    allTrues = Set.union trueVars $ Set.fromList [true]
    allFalses = Set.union falseVars $ Set.fromList [false]

-- | Check whether a branch is closed, based on assigned values
isClosed :: LineSet -> Bool
isClosed proofLineSets = not $ Set.disjoint (trues interpretations) (falses interpretations)
  where
    interpretations = getInterpretations proofLineSets

-- | Check whether branch is open
isOpen :: LineSet -> Bool
isOpen label@(LineSet lns) = not (isClosed label) && fullyExpanded lns
  where
    fullyExpanded :: [Line] -> Bool
    fullyExpanded [] = True
    -- True universal expansion doesn't leave the branch
    -- So, check if we can apply the rule to any new objects
    fullyExpanded ((UnFinally (T (Universally _ _ ts))) : xs)
        | null ts = False
        | ts == free label = fullyExpanded xs
        | otherwise = False
    fullyExpanded ((UnFinally _) : _) = False
    fullyExpanded ((Then _ _) : _) = False
    fullyExpanded (_ : xs) = fullyExpanded xs

-- | Children for recursion by expanding thens
getChildren :: LineSet -> Branched
getChildren (LineSet lns) = Branched (map LineSet nestedSteps)
  where
    nestedSteps = combineThens [[]] lns

    isThen (Then _ _) = True
    isThen _ = False

    fromThen :: Line -> [[Line]]
    fromThen (Then _ (Branched b)) = [b' | (LineSet b') <- b]
    fromThen _ = error "Not a Then"

    -- Recursive helper
    combineThens :: [[Line]] -> [Line] -> [[Line]]
    combineThens acc [] = acc
    combineThens acc (x : xs)
        | isThen x = combineThens ([existing ++ new | existing <- acc, new <- fromThen x]) xs
        | otherwise = combineThens (map (++ [x]) acc) xs

-- | Recursively prove
-- prove :: Int -> LineSet -> ProofNode
-- prove depth label@(LineSet xs)
--     | depth <= 0 = Proof label Cutoff Nothing
--     | isClosed proof = Proof label Closed Nothing
--     | isOpen proof = Proof label (Open [interpretations]) Nothing
--     | childIsOpen = Proof label (Open openChildInterpretations) (Just provenChildren)
--     | childrenAreClosed = Proof label Closed (Just provenChildren)
--     | otherwise = Proof label Cutoff Nothing -- TODO: WHAT CASE IS THIS
--   where
--     proof :: LineSet
--     proof = LineSet [step `finalise` label | step <- xs]
--
--     (Branched bs) = getChildren proof
--
--     provenChildren = map (prove $ depth - 1) bs
--
--     isLiteralOpen :: ProofNode -> Bool
--     isLiteralOpen node = case nodeValue node of
--         (Open _) -> True
--         _ -> False
--
--     isLiteralClosed :: ProofNode -> Bool
--     isLiteralClosed node = case nodeValue node of
--         Closed -> True
--         _ -> False
--
--     openChildren = filter isLiteralOpen provenChildren
--     childIsOpen = any isLiteralOpen provenChildren
--
--     childrenAreClosed = all isLiteralClosed provenChildren
--
--     interpretations = getInterpretations proof
--
--     fromLineSet :: ProofNode -> [Interpretations]
--     fromLineSet node = case nodeValue node of
--         (Open a) -> a
--         _ -> error "Not a singleton Open"
--
--     openChildInterpretations = concatMap fromLineSet openChildren

-- | Recursively prove
prove :: Int -> LineSet -> ProofNode
prove depth node@(LineSet lns)
    | depth <= 0 = basicProof {nodeValue = Cutoff}
    | isClosed node = basicProof {nodeValue = Closed}
    | isOpen node = basicProof {nodeValue = Open [getInterpretations node]}
    | otherwise = case (openChild, cutoffChild) of
        (Nothing, Nothing) -> basicProof {nodeValue = Closed, children = Just provenChildren}
        (Nothing, Just child) -> basicProof {nodeValue = Cutoff, children = Just provenChildren}
        (Just child, _) -> basicProof {nodeValue = nodeValue child, children = Just provenChildren}
    where
        -- Partially constructed proof for current node
        finalisedLines = LineSet [ln `finalise` node | ln <- lns]
        basicProof = Proof {curLines = finalisedLines, expandedLines = LineSet [], children = Nothing, nodeValue = Cutoff}

        -- Recurse over children until a counter-model is found
        proofChildren = getChildren finalisedLines
        provenChildren = takeWhileAddOne (not . isOpen . allLines) $ map (prove (depth - 1)) $ unBranched proofChildren

            where
                -- Helper: takeWhile + take one more
                takeWhileAddOne :: (t -> Bool) -> [t] -> [t]
                takeWhileAddOne _ [] = []
                takeWhileAddOne p ls = case dropped of
                    [] -> taken
                    (x:_) -> taken ++ [x]
                    where
                        (taken, dropped) = span p ls

        -- The child which was open
        openChild = List.find returnedOpen provenChildren
            where
                returnedOpen :: ProofNode -> Bool
                returnedOpen c = case nodeValue c of
                    (Open _) -> True
                    _ -> False

        -- Child which cutoff
        cutoffChild = List.find returnedCutoff provenChildren
            where
                returnedCutoff :: ProofNode -> Bool
                returnedCutoff c = case nodeValue c of
                    Cutoff -> True
                    _ -> False




-- mergedInterpretations =
--     foldl
--         (\(Interpretations t f) (Interpretations t' f') -> Interpretations (t `Set.union` t') (f `Set.union` f'))
--         (Interpretations Set.empty Set.empty)
--         openChildInterpretations

-- | Setup a proof from a sequent
setupProof :: Sequent -> LineSet
setupProof (Entails a b) = LineSet $ UnFinally (F b) : [UnFinally (T x) | x <- a]

-- | Check if a sequent is valid
isValid :: Sequent -> Maybe Bool
isValid s = case nodeValue $ proveSequent s of
    Closed -> Just True
    (Open _) -> Just False
    _ -> Nothing

idDfsProve :: Int -> Int -> LineSet -> ProofNode
idDfsProve depth maxDepth ls = case nodeValue result of
    Closed -> result
    (Open _) -> result
    Cutoff
        | depth >= maxDepth -> result
        | otherwise -> idDfsProve (depth + 1) maxDepth ls
    where
        result = prove depth ls

-- | Prove a sequent
proveSequent :: Sequent -> ProofNode
proveSequent = idDfsProve 1 99 . setupProof
