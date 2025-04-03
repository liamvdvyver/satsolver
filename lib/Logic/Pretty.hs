{-# LANGUAGE FlexibleInstances #-}

module Logic.Pretty (pretty, prettyInts) where

import Logic
import Logic.Proofs

import qualified Data.List as List
import qualified Data.Set as Set

class Pretty t where
    pretty :: t -> String

instance Pretty String where
    pretty = id

commaSeparate :: (Pretty t) => [t] -> String
commaSeparate [] = ""
commaSeparate (x : xs) = pretty x ++ List.intercalate ", " (map pretty xs)

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
    pretty (p `And` q) = pretty p ++ "∧" ++ pretty q
    pretty (p `Or` q) = pretty p ++ "∨" ++ pretty q
    pretty (Not p) = "¬" ++ pretty p
    pretty (p `Implies` q) = pretty p ++ "→" ++ pretty q
    pretty (p `Iff` q) = pretty p ++ "↔" ++ pretty q
    pretty (Predication predicate terms) = pretty predicate ++ inBrackets (commaSeparate terms)
    pretty (Existentially t f) = "∃" ++ pretty t ++ (inBrackets . pretty) f
    pretty (Universally t f _) = "∀" ++ pretty t ++ (inBrackets . pretty) f

instance Pretty Sequent where
    pretty (x `Entails` y) = commaSeparate x ++ "|-" ++ pretty y

instance Pretty Signed where
    pretty (T f) = "T: " ++ pretty f
    pretty (F f) = "F: " ++ pretty f

prettyInts :: [Interpretations] -> String
prettyInts i = commaSeparate (map pretty' i)
  where
    pretty' (ts, fs) = "(" ++ prettyTs ++ ", " ++ prettyFs ++ ")"
      where
        prettyTs = commaSeparate $ Set.toList $ Set.map (("T: " ++) . pretty) ts
        prettyFs = commaSeparate $ Set.toList $ Set.map (("F: " ++) . pretty) fs

instance Pretty ProofStep where
    pretty (Finally s) = pretty s
    pretty (UnFinally s) = inBrackets s
    pretty (Then s _) = inBrackets s ++ " (branch) "
    pretty (Open i) = "Model :" ++ prettyInts i
    pretty Closed = "Closed"
    pretty Cutoff = "(Cutoff)"

instance Pretty ProofNode where
    pretty (Proof label _ children) = unlines $ labelText : childrenText
      where
        labelText = unlines $ map pretty label
        indent = "    "
        childrenText :: [String]
        childrenText = map (indent ++) $ concatMap lines $ case children of
            Nothing -> []
            Just c -> map pretty c
