module Solver where

import Data.Char
import Data.List as List
import qualified Data.Set as Set
import Types

data ProofLine = T Formula | F Formula
    deriving (Show, Eq, Ord)

data ProofNode
    = Then ProofLine Alternates -- A Line which branches to several sub-proofs
    | UnFinally ProofLine -- Line which still may branch
    | Finally ProofLine -- Line which is known not to branch
    | Open [Interpretations] -- Keep track of variable assignment to find counterexample
    | Closed
    deriving (Show, Eq)

type Alternates = [Consecutives] -- Branched Possibilities
type Consecutives = [ProofNode]
type Interpretations = (Set.Set Formula, Set.Set Formula) -- (trues, falses)

{- | Subsitiute a term in a formula recursively

>>> let a = FunctionApplication (Function "a" 0) []
>>> let b = FunctionApplication (Function "b" 0) []
>>> let x = Var "x"
>>> substitute (Predication (Predicate "P" 1) [a]) a b
Predication (Predicate "P" 1) [FunctionApplication (Function "b" 0) []]
>>> substitute ((Predication (Predicate "P" 1) [a]) `And` (Predication (Predicate "P" 1) [b])) a b
And (Predication (Predicate "P" 1) [FunctionApplication (Function "b" 0) []]) (Predication (Predicate "P" 1) [FunctionApplication (Function "b" 0) []])
>>> substitute (Universally (Var "a") (Predication (Predicate "P" 1) [a]) Set.empty) (Var "a") b
Universally (Var "a") (Predication (Predicate "P" 1) [FunctionApplication (Function "a" 0) []]) (fromList [])
-}
substitute :: Formula -> Term -> Term -> Formula
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
substitute (Predication predicate terms) from to = Predication predicate $ map subTerm terms
  where
    subTerm :: Term -> Term
    subTerm term
        | term == from = to
        | otherwise = case term of
            Var s -> Var s
            FunctionApplication function terms' -> FunctionApplication function $ map subTerm terms'

{- | Find terms in branch

>>> let p = Predication (Predicate "P" 0) []
>>> let q = Predication (Predicate "Q" 0) []
>>> let a = FunctionApplication (Function "a" 0) []
>>> let x = Var "x"
>>> let fa = Predication (Predicate "F" 1) [a]
>>> let fx = Predication (Predicate "F" 1) [x]
>>> let u = Universally x fx Set.empty
>>> let ua = Universally (Var "x") fx $ Set.singleton a
>>> branchTerms [Finally $ T fa, UnFinally $ T u] == Set.fromList [x, a]
True
-}
branchTerms :: Consecutives -> Set.Set Term
branchTerms lns = Set.fromList $ concatMap lineTerms lns
  where
    lineTerms (Finally (T formula)) = formulaTerms formula
    lineTerms (Finally (F formula)) = formulaTerms formula
    lineTerms (UnFinally (T formula)) = formulaTerms formula
    lineTerms (UnFinally (F formula)) = formulaTerms formula
    lineTerms (Then (T formula) _) = formulaTerms formula
    lineTerms (Then (F formula) _) = formulaTerms formula
    lineTerms Closed = []
    lineTerms (Open _) = []

    formulaTerms :: Formula -> [Term]
    formulaTerms (And a b) = formulaTerms a ++ formulaTerms b
    formulaTerms (Or a b) = formulaTerms a ++ formulaTerms b
    formulaTerms (Not a) = formulaTerms a
    formulaTerms (Implies a b) = formulaTerms a ++ formulaTerms b
    formulaTerms (Iff a b) = formulaTerms a ++ formulaTerms b
    formulaTerms (Existentially _ formula) = formulaTerms formula
    formulaTerms (Universally _ formula _) = formulaTerms formula
    formulaTerms (Predication _ t) = concatMap termTerms t

    termTerms :: Term -> [Term]
    termTerms v@(Var _) = [v]
    termTerms f@(FunctionApplication _ ts) = f : concatMap termTerms ts

-- | Find functions in branch
branchFunctions :: Consecutives -> Set.Set Function
branchFunctions lns = Set.fromList $ concatMap getFunction $ branchTerms lns
  where
    getFunction :: Term -> [Function]
    getFunction (FunctionApplication f _) = [f]
    getFunction _ = []

-- | Instantiate new object to branch
newObject :: Consecutives -> Term
newObject lns = FunctionApplication (Function newName 0) []
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

{- | Get the (multiples) lines (for multiple branches) which follow from a line of a proof

>>> branchLine (T (Predication (Predicate "P" 0) [] `Iff` Predication (Predicate "Q" 0) [])) []
[[UnFinally (T (Predication (Predicate "P" 0) [])),UnFinally (T (Predication (Predicate "Q" 0) []))],[UnFinally (F (Predication (Predicate "P" 0) [])),UnFinally (F (Predication (Predicate "Q" 0) []))]]
-}
branchLine :: ProofLine -> Consecutives -> Alternates
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
    (T (Existentially v a)) -> [[T $ substitute a v obj]]
      where
        obj = newObject branch
    -- Add line for each object in the branch, and keep
    -- Then keep this here since we need to apply to later instantiated objects
    -- Branches can still close with this behaviour
    -- But in checking for openness, we just need to check that there are no
    -- further object to apply the rule to
    -- TODO: We will probably need to branch into a set
    (T (Universally v a applied)) -> [T (Universally v a (Set.union applied terms)) : fs]
      where
        terms = branchTerms branch
        fs = Set.toList $ Set.map (T . substitute a v) terms
    -- Non-simplifying proof lines
    (T _) -> error "Interpretation of predicate does not branch"
    (F _) -> error "Interpretation of predciate does not branch"

{- | Turn an unFinally into a subproof, i.e. a list containing Finally or a Then (applying one step of simplification)

>>> finalise (UnFinally (T (Predication (Predicate "P" 0) []))) []
Finally (T (Predication (Predicate "P" 0) []))
>>> finalise (Finally (T (Predication (Predicate "P" 0) []))) []
Finally (T (Predication (Predicate "P" 0) []))
>>> finalise (UnFinally (T (Or (Predication (Predicate "P" 0) []) (Predication (Predicate "Q" 0) [])))) []
Then (T (Or (Predication (Predicate "P" 0) []) (Predication (Predicate "Q" 0) []))) [[UnFinally (T (Predication (Predicate "P" 0) []))],[UnFinally (T (Predication (Predicate "Q" 0) []))]]
-}
finalise :: ProofNode -> [ProofNode] -> ProofNode
finalise (UnFinally f@(T (Predication _ _))) _ = Finally f
finalise (UnFinally f@(F (Predication _ _))) _ = Finally f
finalise (UnFinally line) branch = Then line $ branchLine line branch
finalise x _ = x

{- | Get a tuple of (True Vars, False Vars)

>>> getInterpretations [Finally $ T (Predication (Predicate "P" 0) []), Finally $ F (Predication (Predicate "P" 0) []), Finally $ T (Predication (Predicate "Q" 0) []), Finally $ T (Predication (Predicate "P" 0) [] `Or` Predication (Predicate "Q" 0) []), UnFinally $ T (Predication (Predicate "Q" 0) [])]
(fromList [Predication (Predicate "P" 0) [],Predication (Predicate "Q" 0) [],Predication (Predicate "T" 0) []],fromList [Predication (Predicate "F" 0) [],Predication (Predicate "P" 0) []])
-}
getInterpretations :: Consecutives -> Interpretations
getInterpretations proofNodes = (trues, falses)
  where
    isInterpretation :: ProofNode -> Bool
    isInterpretation (Finally (T (Predication _ _))) = True
    isInterpretation (Finally (F (Predication _ _))) = True
    isInterpretation _ = False

    fromFinally :: ProofNode -> ProofLine
    fromFinally (Finally a) = a
    fromFinally _ = error "Not Finally"

    isTrue :: ProofLine -> Bool
    isTrue (T _) = True
    isTrue (F _) = False

    fromProofLine :: ProofLine -> Formula
    fromProofLine (T a@(Predication _ _)) = a
    fromProofLine (F a@(Predication _ _)) = a
    fromProofLine ln = error $ "Not an interpretation" ++ show ln

    interpretations = map fromFinally $ filter isInterpretation proofNodes
    trueVars = Set.fromList $ map fromProofLine $ filter isTrue interpretations
    falseVars = Set.fromList $ map fromProofLine $ filter (not . isTrue) interpretations

    trues = Set.union trueVars $ Set.fromList [Predication (Predicate "T" 0) []]
    falses = Set.union falseVars $ Set.fromList [Predication (Predicate "F" 0) []]

{- | Check whether a branch is closed, based on assigned values

>>> isClosed [Finally $ T $ Predication (Predicate "P" 0) [], Finally $ F $ Predication (Predicate "P" 0) []]
True
>>> isClosed [Finally $ T $ Predication (Predicate "P" 0) [], UnFinally $ F $ Predication (Predicate "P" 0) []]
False
-}
isClosed :: Consecutives -> Bool
isClosed proofNodes = not $ Set.disjoint trues falses
  where
    (trues, falses) = getInterpretations proofNodes

{- | Check whether branch is open

>>> let p = Predication (Predicate "P" 0) []
>>> let q = Predication (Predicate "Q" 0) []
>>> let a = FunctionApplication (Function "a" 0) []
>>> let x = Var "x"
>>> let fa = Predication (Predicate "F" 1) [a]
>>> let fx = Predication (Predicate "F" 1) [x]
>>> let u = Universally x fx Set.empty
>>> let ua = Universally (Var "x") fx $ Set.fromList [x, a]
>>> isOpen [Finally $ T p, Finally $ F q]
True
>>> isOpen [Finally $ T p, Finally $ F p]
False
>>> isOpen [Finally $ T p, Finally $ F q, UnFinally $ T p]
False
>>> isOpen [Finally $ T p, Then (F $ p `Or` q) [[UnFinally $ F p, UnFinally $ F q]]]
False
>>> isOpen [Finally $ T p, UnFinally $ F p, UnFinally $ F q]
False
>>> isOpen [UnFinally $ T u, Finally $ T fa]
False
>>> isOpen [UnFinally $ T ua, Finally $ T fa]
True
-}
isOpen :: Consecutives -> Bool
isOpen proofNodes = not (isClosed proofNodes) && fullyExpanded proofNodes
  where
    fullyExpanded :: Consecutives -> Bool
    fullyExpanded [] = True
    -- True universal expansion doesn't leave the branch
    -- So, check if we can apply the rule to any new objects
    fullyExpanded ((UnFinally (T (Universally _ _ ts))) : xs)
        | ts == branchTerms proofNodes = fullyExpanded xs
        | otherwise = False
    fullyExpanded ((UnFinally _) : _) = False
    fullyExpanded ((Then _ _) : _) = False
    fullyExpanded (_ : xs) = fullyExpanded xs

{- | Number of branches to be explored when expanding a Then
TODO:  Use this to branch as late as possible
-}
nBranches :: ProofNode -> Int
nBranches (Then _ b) = length b
nBranches _ = 1

{- | Children for recursion by expanding thens

>>> getChildren [(Finally $ T $ (Predication (Predicate "P" 0) [])), Then (F $ (Predication (Predicate "P" 0) []) `Or` (Predication (Predicate "Q" 0) [])) [[(UnFinally $ F $ Predication (Predicate "P" 0) []), (UnFinally $ F $ Predication (Predicate "Q" 0) [])]]]
[[Finally (T (Predication (Predicate "P" 0) [])),UnFinally (F (Predication (Predicate "P" 0) [])),UnFinally (F (Predication (Predicate "Q" 0) []))]]
-}
getChildren :: Consecutives -> Alternates
getChildren = combineThens [[]]
  where
    isThen (Then _ _) = True
    isThen _ = False

    fromThen :: ProofNode -> Alternates
    fromThen (Then _ b) = b
    fromThen _ = error "Not a Then"

    -- Recursive helper
    combineThens :: Alternates -> Consecutives -> Alternates
    combineThens acc [] = acc
    combineThens acc (x : xs)
        | isThen x = combineThens ([existing ++ new | existing <- acc, new <- fromThen x]) xs
        | otherwise = combineThens (map (++ [x]) acc) xs

{- | Recursively prove

>>> prove 99 [(Finally $ T $ (Predication (Predicate "P" 0) [])), (UnFinally $ F $ (Predication (Predicate "P" 0) []) `And` (Predication (Predicate "Q" 0) []))]
[Open [(fromList [Predication (Predicate "P" 0) [],Predication (Predicate "T" 0) []],fromList [Predication (Predicate "F" 0) [],Predication (Predicate "Q" 0) []])]]
>>> prove 99 [(Finally $ T $ (Predication (Predicate "P" 0) [])), (Finally $ F $ Predication (Predicate "P" 0) []), (Finally $ F $ Predication (Predicate "Q" 0) [])]
[Closed]
>>> prove 99 [(Finally $ T $ (Predication (Predicate "P" 0) [])), (UnFinally $ F $ Predication (Predicate "P" 0) []), (UnFinally $ F $ Predication (Predicate "Q" 0) [])] -- The child
[Closed]
>>> prove 99 [(Finally $ T $ (Predication (Predicate "P" 0) [])), Then (F $ (Predication (Predicate "P" 0) []) `Or` (Predication (Predicate "Q" 0) [])) [[(UnFinally $ F $ Predication (Predicate "P" 0) []), (UnFinally $ F $ Predication (Predicate "Q" 0) [])]]] -- The parent
[Closed]
>>> prove 99 [(Finally $ T $ (Predication (Predicate "P" 0) [])), (UnFinally $ F $ (Predication (Predicate "P" 0) []) `Or` (Predication (Predicate "Q" 0) []))]
[Closed]
-}
prove :: Int -> Consecutives -> Consecutives
prove depth xs
    | depth <= 0 = []
    | isClosed proof = pure Closed
    | isOpen proof = pure $ Open [interpretations]
    | childIsOpen = pure $ Open mergedInterpretations
    | childrenAreClosed = pure Closed
    | otherwise = []
  where
    proof = map (`finalise` xs) xs

    children = getChildren proof

    provenChildren = map (prove $ depth - 1) children

    isLiteralOpen [Open _] = True
    isLiteralOpen _ = False
    openChildren = filter isLiteralOpen provenChildren
    childIsOpen = any isLiteralOpen provenChildren

    childrenAreClosed = all (== [Closed]) provenChildren

    interpretations = getInterpretations proof
    fromNode [Open a] = a
    fromNode _ = error "Not a singleton Open"

    openChildInterpretations = map fromNode openChildren
    mergedInterpretations = foldl List.union [] openChildInterpretations

-- | Setup a proof from a sequent
setupProof :: Sequent -> Consecutives
setupProof (Entails a b) = UnFinally (F b) : [UnFinally (T x) | x <- a]

{- | Check if a sequent is valid

>>> isValid $ [(Not $ (Predication (Predicate "P" 0) []) `Or` (Predication (Predicate "Q" 0) []))] `Entails` ((Not $ Predication (Predicate "P" 0) []) `And` (Not $ Predication (Predicate "Q" 0) []))
True
>>> isValid $ [(((Predication (Predicate "P" 0) []) `Or` (Predication (Predicate "Q" 0) [])) `Iff` ((Predication (Predicate "R" 0) []) `Or` (Predication (Predicate "S" 0) [])))] `Entails` (((Predication (Predicate "P" 0) []) `Iff` (Predication (Predicate "R" 0) [])) `Or` ((Predication (Predicate "Q" 0) []) `Iff` (Predication (Predicate "S" 0) [])))
False
-}
isValid :: Sequent -> Bool
isValid s = case proveSequent s of
    [Open _] -> False
    [Closed] -> True
    _ -> error "Did not reduce"

idDfsProve :: Int -> Int -> Consecutives -> Consecutives
idDfsProve depth maxDepth xs = case proven of
    (Closed : _) -> proven
    (Open _ : _) -> proven
    _
        | depth >= maxDepth -> proven
        | otherwise -> idDfsProve (depth + 1) maxDepth xs
  where
    proven = prove depth xs

{- | Prove a sequent

>>> proveSequent $ [(((Predication (Predicate "P" 0) []) `Or` (Predication (Predicate "Q" 0) [])) `Iff` ((Predication (Predicate "R" 0) []) `Or` (Predication (Predicate "S" 0) [])))] `Entails` (((Predication (Predicate "P" 0) []) `Iff` (Predication (Predicate "R" 0) [])) `Or` ((Predication (Predicate "Q" 0) []) `Iff` (Predication (Predicate "S" 0) [])))
[Open [(fromList [Predication (Predicate "P" 0) [],Predication (Predicate "S" 0) [],Predication (Predicate "T" 0) []],fromList [Predication (Predicate "F" 0) [],Predication (Predicate "Q" 0) [],Predication (Predicate "R" 0) []]),(fromList [Predication (Predicate "Q" 0) [],Predication (Predicate "R" 0) [],Predication (Predicate "T" 0) []],fromList [Predication (Predicate "F" 0) [],Predication (Predicate "P" 0) [],Predication (Predicate "S" 0) []])]]
-}
proveSequent :: Sequent -> Consecutives
proveSequent = (idDfsProve 1 99) . setupProof
