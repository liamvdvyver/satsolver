module Parser (parseSequent, parseFormula, tokenise) where

import Solver

-- | Identifier ::= Char
data Token
    = Identifier Char
    | LeftParen
    | RightParen
    | Bang
    | Pipe
    | Ampersand
    | Equals
    | RightAngle
    | Turnstile
    | Truth
    | Falsity
    | Comma
    deriving (Show, Eq)

tokenise :: String -> [Token]
tokenise "" = []
tokenise (' ' : xs) = tokenise xs
tokenise ('|' : '-' : xs) = Turnstile : tokenise xs
tokenise (x : xs) = matched : tokenise xs
  where
    matched = case x of
        '(' -> LeftParen
        ')' -> RightParen
        '!' -> Bang
        '|' -> Pipe
        '&' -> Ampersand
        '=' -> Equals
        '>' -> RightAngle
        'T' -> Truth
        'F' -> Falsity
        ',' -> Comma
        c -> Identifier c

type FormulaParser = [Token] -> (Formula, [Token])

-- | To apply connective to output of call to parser
mapFst :: (a -> a) -> (a, b) -> (a, b)
mapFst f (a, b) = (f a, b)

{- | Atom ::= Identifier | "T" | "F"

>>> parseAtom [Identifier 'a']
(FromAtom (Var 'a'),[])
>>> parseAtom [Truth]
(FromAtom ConstTrue,[])
-}
parseAtom :: FormulaParser
parseAtom [] = error "Parse error: empty atom"
parseAtom (t : ts) = (FromAtom atom, ts)
  where
    atom = case t of
        (Identifier a) -> Var a
        Truth -> ConstTrue
        Falsity -> ConstFalse
        _ -> error "Parse error: expected atom"

{- | Grouping ::= "(" Formula ")"

>>> parseGrouping [LeftParen, Identifier 'a', RightParen, Identifier 'b']
(FromAtom (Var 'a'),[Identifier 'b'])
-}
parseGrouping :: FormulaParser
parseGrouping [] = error "Parse error: empty grouping"
parseGrouping (LeftParen : ts) = case parseFormula ts of
    (f, RightParen : xs) -> (f, xs)
    _ -> error "Parse error: expected ')'"
parseGrouping _ = error "Parse error: expected '('"

{- | Primary ::= Atom | Grouping

>>> parsePrimary [Identifier 'a', Identifier 'b']
(FromAtom (Var 'a'),[Identifier 'b'])
>>> parsePrimary [LeftParen, Identifier 'a', RightParen, Identifier 'b']
(FromAtom (Var 'a'),[Identifier 'b'])
-}
parsePrimary :: FormulaParser
parsePrimary [] = error "Parse error: empty primary formula"
parsePrimary xs@(t : _) = case t of
    LeftParen -> parseGrouping xs
    _ -> parseAtom xs

-- | Negation ::= "!" Negation | Primary
parseNegation :: FormulaParser
parseNegation [] = error "Parse error: empty negation"
parseNegation (Bang : ts) = mapFst Not $ parseNegation ts
parseNegation ts = parsePrimary ts

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

-- | Conjunction ::= Negation ("&" Negation)*
parseConjunction :: FormulaParser
parseConjunction ts = binaryParse ts Ampersand And parseNegation

-- | Disjunction ::= Conjunction ("|" Conjunction)*
parseDisjunction :: FormulaParser
parseDisjunction ts = binaryParse ts Pipe Or parseConjunction

-- | Implication ::= Disjunction (">" Disjunction)*
parseImplication :: FormulaParser
parseImplication ts = binaryParse ts RightAngle Implies parseDisjunction

-- | Equivalence ::= Implication ("=" Implication)*
parseEquivalence :: FormulaParser
parseEquivalence ts = binaryParse ts Equals Iff parseImplication

-- | Formula ::= Equivalence
parseFormula :: FormulaParser
parseFormula = parseEquivalence

-- | Sequent ::= Formula ("," Formula)* "|-" Formula
--
-- >>> parseSequent $ tokenise $ "X|-a"
-- Entails [FromAtom (Var 'X')] (FromAtom (Var 'a'))
-- >>> parseSequent $ tokenise $ "X,Y|-a"
-- Entails [FromAtom (Var 'X'),FromAtom (Var 'Y')] (FromAtom (Var 'a'))
-- >>> parseSequent $ tokenise $ "|-a"
-- Entails [] (FromAtom (Var 'a'))
parseSequent :: [Token] -> Sequent
parseSequent ts = Entails leftFormulae finalRightFormula
    where
    (leftFormulae, finalRightFormula) = parseLhs [] ts

    parseLhs :: [Formula] -> [Token] -> ([Formula], Formula)
    parseLhs parsed (Turnstile:ts') = (parsed, parseRhs ts')
    parseLhs parsed (Comma:ts') = parseLhs parsed ts'
    parseLhs [] ts' = parseLhs [parsed'] remainder
        where (parsed', remainder) = parseFormula ts'
    parseLhs parsed ts' = parseLhs (parsed ++ [parsed']) remainder
        where (parsed', remainder) = parseFormula ts'

    parseRhs :: [Token] -> Formula
    parseRhs ts' = case parseFormula ts' of
        (f, []) -> f
        (_, _) -> error "Parse Error: Trailing tokens in RHS of sequent"
