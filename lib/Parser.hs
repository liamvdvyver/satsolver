module Parser (parseSequent, parseFormula, tokenise) where

import Data.Char
import qualified Data.Set as Set
import Types

{- The complete grammar:

Variable ::= Identifier
Function ::= Identifier "(" Function ("," Function)* ")" | Variable
Predicate ::= Identifier ("(" Function ("," Function)* ")")?
Grouping ::= "(" Formula ")" | Predicate
Negation ::= "!" Negation | Grouping
Quantification ::= ("E" | "V") Variable Quantification | Negation
Conjunction ::= Quantification ("&" Quantification)*
Disjunction ::= Conjunction ("|" Conjunction)*
Implication ::= Disjuntion ("->" Disjunction)*
Equivalence ::= Implication ("=" Implication)*
Formula ::= Equivalence
Sequent ::= Formula ("," Formula)* "|-" Formula

-}

data Token
    = Identifier Identifier
    | LeftParen
    | RightParen
    | Bang
    | Pipe
    | Ampersand
    | Equals
    | DoubleArrow
    | RightArrow
    | Turnstile
    | Comma
    | Exists
    | Forall
    deriving (Show, Eq)

tokenise :: String -> [Token]
tokenise "" = []
tokenise (' ' : xs) = tokenise xs
tokenise ('|' : '-' : xs) = Turnstile : tokenise xs
tokenise ('<' : '>' : xs) = DoubleArrow : tokenise xs
tokenise ('-' : '>' : xs) = RightArrow : tokenise xs
tokenise ('(' : xs) = LeftParen : tokenise xs
tokenise (')' : xs) = RightParen : tokenise xs
tokenise ('!' : xs) = Bang : tokenise xs
tokenise ('|' : xs) = Pipe : tokenise xs
tokenise ('&' : xs) = Ampersand : tokenise xs
tokenise ('=' : xs) = Equals : tokenise xs
tokenise (',' : xs) = Comma : tokenise xs
tokenise ('E' : xs) = Exists : tokenise xs
tokenise ('V' : xs) = Forall : tokenise xs
tokenise str@(x : _)
    | not $ isAlphaNum x = error $ "Parse error: " ++ str
    | otherwise = Identifier ident : tokenise remainder
  where
    (ident, remainder) = span isAlphaNum str

type FormulaParser = [Token] -> (Formula, [Token])
type TermParser = [Token] -> (Term, [Token])

-- | To apply connective to output of call to parser
mapFst :: (a -> a) -> (a, b) -> (a, b)
mapFst f (a, b) = (f a, b)

parseVar :: TermParser
parseVar ((Identifier str) : xs) = (Var str, xs)
parseVar [] = error "Parse error: empty variable"
parseVar _ = error "Parse error: expected identifier"

-- | Helper for predicates/function
parseTerms :: [Token] -> ([Term], [Token])
parseTerms [] = error "Parse error: empty terms"
parseTerms (LeftParen : tokens) = parseTerms' [] tokens
  where
    parseTerms' :: [Term] -> [Token] -> ([Term], [Token])
    parseTerms' _ [] = error "Parse error: empty terms"
    parseTerms' acc tokens'@(t : ts) = case t of
        RightParen -> (acc, ts)
        Comma -> parseTerms' acc ts
        _ -> parseTerms' (acc ++ [term]) remainder
          where
            (term, remainder) = parseFunction tokens'
parseTerms _ = error "Parse error: expected '('"

parseFunction :: TermParser
parseFunction [] = error "Parse error: empty function"
parseFunction ((Identifier str) : ts@(LeftParen : _)) = (FunctionApplication (Function str arity) terms, remainder)
  where
    (terms, remainder) = parseTerms ts
    arity = length terms
parseFunction ts = parseVar ts

parsePredicate :: FormulaParser
parsePredicate [] = error "Parse error: empty Predicate"
parsePredicate ((Identifier str) : ts@(LeftParen : _)) = (Predication (Predicate str arity) terms, remainder)
  where
    (terms, remainder) = parseTerms ts
    arity = length terms
parsePredicate (Identifier str : ts) = (Predication (Predicate str 0) [], ts)
parsePredicate _ = error "Parse error: expected identifier"

-- | Grouping ::= "(" Formula ")" | Predicate
parseGrouping :: FormulaParser
parseGrouping [] = error "Parse error: empty grouping"
parseGrouping (LeftParen : ts) = case parseFormula ts of
    (f, RightParen : xs) -> (f, xs)
    _ -> error "Parse error: expected ')'"
parseGrouping ts = parsePredicate ts

parseNegation :: FormulaParser
parseNegation [] = error "Parse error: empty negation"
parseNegation (Bang : ts) = mapFst Not $ parseNegation ts
parseNegation ts = parseGrouping ts

parseQuantification :: FormulaParser
parseQuantification [] = error "Parse error: empty qualification"
parseQuantification tokens@(t : ts) =
    let
        (var, xs') = parseVar ts
        (formula, remainder) = parseNegation xs'
     in
        case t of
            Exists -> (Existentially var formula, remainder)
            Forall -> (Universally var formula Set.empty, remainder)
            _ -> parseNegation tokens

-- | Build parser for binary connective based on precedence
binaryParse ::
    [Token] ->
    Token ->
    (Formula -> Formula -> Formula) ->
    FormulaParser ->
    (Formula, [Token])
binaryParse [] _ _ _ = error "Parse error: empty binary formula"
binaryParse ts operator constructor nextParser
    | headLeftRemainder == Just operator =
        (constructor leftFormula rightFormula, rightRemainder)
    | otherwise = (leftFormula, leftRemainder)
  where
    (leftFormula, leftRemainder) = nextParser ts

    headLeftRemainder :: Maybe Token
    tailLeftRemainder :: [Token]
    (headLeftRemainder, tailLeftRemainder) = case leftRemainder of
        [] -> (Nothing, [])
        (x : xs) -> (Just x, xs)

    (rightFormula, rightRemainder) = nextParser tailLeftRemainder

parseConjunction :: FormulaParser
parseConjunction ts = binaryParse ts Ampersand And parseQuantification

parseDisjunction :: FormulaParser
parseDisjunction ts = binaryParse ts Pipe Or parseConjunction

parseImplication :: FormulaParser
parseImplication ts = binaryParse ts RightArrow Implies parseDisjunction

parseEquivalence :: FormulaParser
parseEquivalence ts = binaryParse ts Equals Iff parseImplication

parseFormula :: FormulaParser
parseFormula = parseEquivalence

-- | Sequent ::= Formula ("," Formula)* "|-" Formula
parseSequent :: [Token] -> Sequent
parseSequent ts = Entails leftFormulae finalRightFormula
  where
    (leftFormulae, finalRightFormula) = parseLhs [] ts

    parseLhs :: [Formula] -> [Token] -> ([Formula], Formula)
    parseLhs parsed (Turnstile : ts') = (parsed, parseRhs ts')
    parseLhs parsed (Comma : ts') = parseLhs parsed ts'
    parseLhs [] ts' = parseLhs [parsed'] remainder
      where
        (parsed', remainder) = parseFormula ts'
    parseLhs parsed ts' = parseLhs (parsed ++ [parsed']) remainder
      where
        (parsed', remainder) = parseFormula ts'

    parseRhs :: [Token] -> Formula
    parseRhs ts' = case parseFormula ts' of
        (f, []) -> f
        (_, _) -> error "Parse Error: Trailing tokens in RHS of sequent"
