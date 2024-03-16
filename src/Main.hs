module Main where

import Solver
import Parser
import System.Environment

main :: IO ()
main = do
    args <- getArgs
    let arg = concat args
    let sequent = parseSequent $ tokenise arg
    print $ proveSequent sequent
