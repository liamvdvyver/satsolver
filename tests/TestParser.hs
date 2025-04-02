module Main where

import Test.Tasty (TestTree, defaultMain, testGroup)
import Test.Tasty.HUnit (Assertable (assert), assertBool, assertEqual, testCase)

import Parser
import Types

main = defaultMain testSequents

testSequents :: TestTree
testSequents =
    testGroup
        "Parse sequents"
        [ testCase "Parse tautology" $
            assertEqual
                []
                (parseSequent $ tokenise "|-a")
                (Entails [] (prop "a"))
        , testCase "Parse single premise" $
            assertEqual
                []
                (parseSequent $ tokenise "X|-a")
                (Entails [prop "X"] (prop "a"))
        , testCase "Parse two premises" $
            assertEqual
                []
                (parseSequent $ tokenise "X,Y|-a")
                (Entails [prop "X", prop "Y"] (prop "a"))
        , testCase "Parse with grouping" $
            assertEqual
                []
                (parseSequent $ tokenise "|-(p&q)|r")
                (Entails [] ((prop "p" `And` prop "q") `Or` prop "r"))
        ]
