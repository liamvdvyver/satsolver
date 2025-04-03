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
    pretty (ApplyFunc f t) = pretty f ++ (inBrackets . commaSeparate) t
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
    pretty (ApplyPred predicate terms) = pretty predicate ++ inBrackets (commaSeparate terms)
    pretty (Existentially t f) = "(∃" ++ pretty t ++ pretty f ++ ")"
    pretty (Universally t f _) = "(∀" ++ pretty t ++ pretty f ++ ")"

instance Pretty Sequent where
    pretty (x `Entails` y) = commaSeparate x ++ "|-" ++ pretty y

instance Pretty Signed where
    pretty (T f) = "T: " ++ pretty f
    pretty (F f) = "F: " ++ pretty f

instance Pretty Model where
    pretty (Model ts fs) = "(" ++ prettyTs ++ ", " ++ prettyFs ++ ")"
      where
        prettyTs = commaSeparate $ Set.toList $ Set.map (("T: " ++) . pretty) ts
        prettyFs = commaSeparate $ Set.toList $ Set.map (("F: " ++) . pretty) fs

instance Pretty Line where
    pretty (Finally s) = pretty s
    pretty (UnFinally s) = pretty s
    pretty (Then s _) = inBrackets s ++ " (branch) "

instance Pretty Branched where
    pretty (Branched bs) = "(" ++ commaSeparate bs ++ ")"

instance Pretty LineSet where
    pretty (LineSet lns) = "(" ++ commaSeparate lns ++ ")"

instance Pretty ProofValue where
    pretty Closed = "Closed"
    pretty (Open _) = "Open"
    pretty Cutoff = "Cutoff"

instance Pretty ProofNode where
    pretty node = unlines $ branchVal : labelText : childrenText
      where
        (LineSet lns) = curLines node
        labelText = unlines $ map pretty lns
        indent = "    "
        childrenText :: [String]
        childrenText = map (indent ++) $ concatMap lines $ case children node of
            Nothing -> []
            Just c -> map pretty c
        branchVal = pretty $ nodeValue node
