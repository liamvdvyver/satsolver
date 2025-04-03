{-# LANGUAGE FlexibleInstances #-}

module Logic.Pretty (pretty, commaSeparate) where

import Logic
import Logic.Proofs

import qualified Data.List as List
import qualified Data.Set as Set

class Pretty t where
    pretty :: t -> String

instance Pretty String where
    pretty = id

commaSeparate :: (Pretty t) => [t] -> String
commaSeparate xs = List.intercalate ", " (map pretty xs)

inBrackets :: (Pretty t) => t -> String
inBrackets x = case str of
    "" -> str
    (_ : _) -> "(" ++ str ++ ")"
  where
    str = pretty x

instance Pretty Term where
    pretty (FunctionApplication f t) = pretty f ++ (inBrackets . commaSeparate) t
    pretty (Var s) = s

instance Pretty Function where
    pretty (Function ident _) = ident

instance Pretty Predicate where
    pretty (Predicate identifier _) = identifier

instance Pretty Formula where
    pretty (p `And` q) = "(" ++ pretty p ++ "∧" ++ pretty q ++ ")"
    pretty (p `Or` q) = "(" ++ pretty p ++ "∨" ++ pretty q ++ ")"
    pretty (Not p) = "¬" ++ pretty p
    pretty (p `Implies` q) = "(" ++ pretty p ++ "→" ++ pretty q ++ ")"
    pretty (p `Iff` q) = "(" ++ pretty p ++ "↔" ++ pretty q ++ ")"
    pretty (Predication predicate terms) = pretty predicate ++ inBrackets (commaSeparate terms)
    pretty (Existentially t f) = "(∃" ++ pretty t ++ pretty f ++ ")"
    pretty (Universally t f _) = "(∀" ++ pretty t ++ pretty f ++ ")"

instance Pretty Sequent where
    pretty (x `Entails` y) = commaSeparate x ++ "|-" ++ pretty y

instance Pretty Signed where
    pretty (T f) = "T: " ++ pretty f
    pretty (F f) = "F: " ++ pretty f

instance Pretty Interpretations where
    pretty (Interpretations ts fs) = "(" ++ prettyTs ++ ", " ++ prettyFs ++ ")"
      where
        prettyTs = commaSeparate $ Set.toList $ Set.map (("T: " ++) . pretty) ts
        prettyFs = commaSeparate $ Set.toList $ Set.map (("F: " ++) . pretty) fs

instance Pretty ProofStep where
    pretty (Finally s) = pretty s
    -- pretty (UnFinally s) = inBrackets s
    pretty (UnFinally s) = pretty s
    pretty (Then s _) = inBrackets s ++ " (branch) "
    pretty (Open i) = "Model :" ++ commaSeparate i
    pretty Closed = "Closed"
    pretty Cutoff = "(Cutoff)"

instance Pretty ProofNode where
    pretty (Proof (Node l) _ children) = unlines $ labelText : childrenText
      where
        labelText = unlines $ map pretty l
        indent = "    "
        childrenText :: [String]
        childrenText = map (indent ++) $ concatMap lines $ case children of
            Nothing -> []
            Just c -> map pretty c
