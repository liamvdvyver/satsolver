module Main where

import Test.Tasty (TestTree, defaultMain, testGroup)
import Test.Tasty.HUnit (Assertable (assert), assertBool, assertEqual, testCase)

import Logic.Solver
import Logic.Proofs
import Logic

import qualified Data.Maybe as Maybe
import qualified Data.Set as Set

-- Constants for testing

a :: Term
a = obj "a"

b :: Term
b = obj "b"

x :: Term
x = Var "x"

p :: Formula
p = prop "p"

q :: Formula
q = prop "q"

r :: Formula
r = prop "r"

s :: Formula
s = prop "s"

u :: Formula
u = Universally x px Set.empty

ua :: Formula
ua = Universally (Var "x") px $ Set.singleton a

pa :: Formula
pa = ApplyPred (Predicate "P" 1) [a]

pb :: Formula
pb = ApplyPred (Predicate "P" 1) [b]

px :: Formula
px = ApplyPred (Predicate "P" 1) [x]

-- Substitution

testSub :: TestTree
testSub =
    testGroup
        "Substitution"
        [ testSubUnaryPredicate
        , testSubConnective
        , testSubQuantified
        ]

testSubUnaryPredicate :: TestTree
testSubUnaryPredicate =
    testCase "Substitute unary predicate" $
        assertEqual
            []
            (substitute pa a b)
            pb

testSubConnective :: TestTree
testSubConnective =
    testCase "Substitute with connective" $
        assertEqual
            []
            (substitute (pa `And` pb) a b)
            (pb `And` pb)

testSubQuantified :: TestTree
testSubQuantified =
    testCase "Substitute with connective" $
        assertEqual
            []
            (substitute (Universally (Var "a") pa Set.empty) (Var "a") b)
            (Universally (Var "a") pa Set.empty)

-- Branching

testBranching :: TestTree
testBranching = testGroup "Branching" [testFreeTerms, testBranchLine]

testFreeTerms :: TestTree
testFreeTerms =
    testCase "Find free terms" $
        assertEqual
            []
            (Set.unions $ map free [Finally $ T pa, UnFinally $ T u])
            (Set.singleton a)

testBranchLine :: TestTree
testBranchLine =
    testCase "Apply branching" $
        assertEqual
            []
            (branchLine (T (p `Iff` q)) (LineSet []))
            (Branched [LineSet [UnFinally (T p), UnFinally (T q)], LineSet [UnFinally (F p), UnFinally (F q)]])

-- Finalisation

testFinalise :: TestTree
testFinalise = testGroup "Finalise line" [testFinalisePred, testFinaliseDone, testFinaliseLong]

testFinalisePred :: TestTree
testFinalisePred =
    testCase "Finalise predicate" $
        assertEqual
            []
            (finalise (UnFinally (T p)) (LineSet []))
            (Finally (T p))

testFinaliseDone :: TestTree
testFinaliseDone =
    testCase "Finalise final predicate" $
        assertEqual
            []
            (finalise (Finally (T p)) (LineSet []))
            (Finally (T p))

testFinaliseLong :: TestTree
testFinaliseLong =
    testCase "Finalise long line" $
        assertEqual
            []
            (finalise (UnFinally (T (Or p q))) (LineSet []))
            (Then (T (Or p q)) (Branched [LineSet [UnFinally (T p)], LineSet [UnFinally (T q)]]))

-- Interpretatons

testInterpretations :: TestTree
testInterpretations = testGroup "Get/check interpretations" [testGetInterpretations, testIsClosed, testIsOpen]

testGetInterpretations :: TestTree
testGetInterpretations =
    testCase "Get interpretations" $
        assertEqual
            []
            (getInterpretations $ LineSet [Finally $ T p, Finally $ F p, Finally $ T q, Finally $ T (p `Or` q), UnFinally $ T q])
            (Model (Set.fromList [p, q, true]) (Set.fromList [false, p]))

testIsClosed :: TestTree
testIsClosed =
    testGroup
        "Is branch closed?"
        [ testCase "Closed branch" $ assertBool [] $ isClosed $ LineSet [Finally $ T p, Finally $ F p]
        , testCase "Not closed branch" $ assertBool [] $ not $ isClosed $ LineSet [Finally $ T p, UnFinally $ F p]
        ]

testIsOpen :: TestTree
testIsOpen =
    testGroup
        "Is branch open?"
        $ testCase [] . assertBool []
            <$> [ isOpen $ LineSet [Finally $ T p, Finally $ F q]
                , not $ isOpen $ LineSet [Finally $ T p, Finally $ F p]
                , not $ isOpen $ LineSet [Finally $ T p, Finally $ F q, UnFinally $ T p]
                , not $ isOpen $ LineSet [Finally $ T p, Then (F $ p `Or` q) (Branched [LineSet [UnFinally $ F p, UnFinally $ F q]])]
                , not $ isOpen $ LineSet [Finally $ T p, UnFinally $ F p, UnFinally $ F q]
                , not $ isOpen $ LineSet [UnFinally $ T u, Finally $ T pa]
                , isOpen $ LineSet [UnFinally $ T ua, Finally $ T pa]
                ]
  where
    ua = Universally (Var "x") px $ Set.singleton a

-- Proving

testProving :: TestTree
testProving = testGroup "Running proofs" [testGetChildren, testProve, testValid, testProveSequent]

testGetChildren :: TestTree
testGetChildren =
    testCase "Get children in proof tree" $
        assertEqual
            []
            (getChildren $ LineSet [Finally $ T p, Then (F $ p `Or` q) (Branched [LineSet [UnFinally $ F p, UnFinally $ F q]])])
            (Branched [LineSet [Finally $ T p, UnFinally $ F p, UnFinally $ F q]])

proofDepth = 99
testProve :: TestTree
testProve =
    testGroup "Run proofs on formulae" $
        (\(a, b) -> testCase [] $ assertEqual [] (nodeValue a) b)
            <$> [
                    ( prove proofDepth $ LineSet [Finally $ T p, UnFinally $ F $ p `And` q]
                    , Open [Model (Set.fromList [p, true]) (Set.fromList [false, q])]
                    )
                ,
                    ( prove proofDepth $ LineSet [Finally $ T p, Finally $ F p, Finally $ F q]
                    , Closed
                    )
                ,
                    ( prove proofDepth $ LineSet [Finally $ T p, UnFinally $ F p, UnFinally $ F q]
                    , Closed
                    )
                ,
                    ( prove proofDepth $ LineSet [Finally $ T p, Then (F $ p `Or` q) (Branched [LineSet [UnFinally $ F p, UnFinally $ F q]])] -- The parent
                    , Closed
                    )
                ,
                    ( prove proofDepth $ LineSet [Finally $ T p, UnFinally $ F $ p `Or` q]
                    , Closed
                    )
                ]

testValid :: TestTree
testValid =
    testGroup
        "Check validity"
        [ testCase "Valid sequent" $ assertBool [] $ Maybe.fromJust $ isValid $ [Not $ p `Or` q] `Entails` (Not p `And` Not q)
        , testCase "Invalid sequent" $
            assertBool [] $
                not $
                    Maybe.fromJust $
                        isValid $
                            [(p `Or` q) `Iff` (r `Or` s)] `Entails` ((p `Iff` r) `Or` (q `Iff` s))
        ]

satProof :: ProofValue -> Bool
satProof v = case v of
    Open _ -> True
    Closed -> False

testProveSequent :: TestTree
testProveSequent =
    testCase "Run proofs on sequent" $
        assertBool
            [] $
            satProof (nodeValue (proveSequent $ [(p `Or` q) `Iff` (r `Or` s)] `Entails` ((p `Iff` r) `Or` (q `Iff` s))))

-- All tests

main =
    defaultMain $
        testGroup
            "All tests"
            [ testSub
            , testBranching
            , testFinalise
            , testInterpretations
            , testProving
            ]
