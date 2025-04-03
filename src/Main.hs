module Main where

import Solver
import Parser
import System.Environment
import Types

proofResult :: ProofNode -> String
proofResult proof = case proof of
        (Proof _ Closed _) -> "Valid"
        (Proof _ (Open int) _) -> "Invalid, with countermodel " ++ prettyInts int
        _ -> "Did not reduce"

main :: IO ()
main = do
    args <- getArgs
    let arg = concat args
    let sequent = parseSequent $ tokenise arg
    let proof = proveSequent sequent

    print $ proofResult proof
    print "Proof:"
    let p = pretty proof
    putStr p
