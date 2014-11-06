module Tct.Its.Data.Rule where


import Control.Monad (void)
import Control.Applicative

import qualified Text.Parsec.Expr as PE

import qualified Tct.Common.Polynomial as P
import Tct.Common.Ring
import qualified Tct.Core.Common.Pretty as PP
import qualified Tct.Core.Common.Parser as PR


type Var  = String
type Poly = P.Polynomial Int Var

type Loc  = String
data Term = Term Loc [Poly]
  deriving (Eq, Ord, Show)

data Atom
  = Eq Poly Poly
  | Gte Poly Poly
  deriving (Eq, Ord, Show)

type Constraint = [Atom]

data Rule = Rule
  { lhs :: Term
  , rhs :: [Term]
  , con :: Constraint }
  deriving (Eq, Ord, Show)


-- Pretty Printing ---------------------------------------------------------------------------------------------------
arrowSym, underSym, andSym :: String
arrowSym = "->"
underSym = ":|:"
andSym   = "&&"


instance PP.Pretty Term where
  pretty (Term f ts) = PP.string f PP.<> PP.tupled (map PP.pretty ts)

ppTerms ::  [Term] -> PP.Doc
ppTerms ts = PP.char 'c' PP.<> PP.int (length ts) PP.<> PP.tupled (map PP.pretty ts)

ppBinop :: (PP.Pretty a1, PP.Pretty a2) => a1 -> String -> a2 -> PP.Doc
ppBinop t1 op t2 = PP.pretty t1 PP.<+> PP.text op PP.<+> PP.pretty t2

instance PP.Pretty Atom where
  pretty (Eq t1 t2)  = ppBinop t1 "=" t2
  pretty (Gte t1 t2) = ppBinop t1 ">=" t2

ppAtoms :: [Atom] -> PP.Doc
ppAtoms [] = PP.empty
ppAtoms as = PP.encloseSep PP.lbracket PP.rbracket (PP.text andSym) (map PP.pretty as)

ppSep :: PP.Doc
ppSep = PP.text arrowSym

instance PP.Pretty Rule where
  pretty (Rule l rs cs) =
    PP.pretty l PP.<+> ppSep PP.<+> ppTerms rs PP.<+> ppAtoms cs

ppRules :: [Rule] -> PP.Doc
ppRules rs = PP.table [(PP.AlignLeft, lhss), (PP.AlignLeft, rhss), (PP.AlignLeft, css)]
  where
    lhss = map (PP.pretty . lhs) rs
    rhss = map ((\p -> ppSpace PP.<> ppSep PP.<> ppSpace PP.<> p) . ppTerms . rhs ) rs
    css  = map (ppAtoms . con ) rs
    ppSpace = PP.string "  "

-- Parsing -----------------------------------------------------------------------------------------------------------

-- prule should parse 
-- f(A,B) -> Com_2(f(A,C),round(A,C)) :|: A >= 1 && B + 1 = A

type Parser = PR.Parsec String ()

pVar :: Parser Poly
pVar = P.variable <$> PR.identifier

pNat :: Parser Poly
pNat = P.constant <$> PR.nat

pSep :: Parser ()
pSep = void (PR.symbol "->")

-- constructs a polynomial over an arbitrary arithmetic expression over: int, var, *, +, -, ()
pPoly :: Parser Poly
pPoly = PE.buildExpressionParser table poly PR.<?> "poly"
  where
    poly = 
      PR.parens pPoly
      PR.<|> pNat
      PR.<|> pVar
    table =
      [ [ unary "-" neg ]
      , [ binaryL "*" mul PE.AssocLeft]
      , [ binaryL "+" add PE.AssocLeft, binaryL "-" sub PE.AssocLeft] ]
    unary fun op = PE.Prefix (PR.reserved fun *> return op)
    binaryL fun op = PE.Infix (PR.reserved fun *> return op)

-- f([poly])
pTerm :: Parser Term
pTerm = (Term <$> PR.identifier <*> PR.parens (pPoly `PR.sepBy` PR.symbol ",")) PR.<?> "term"
  
-- Com_nat([terms])
pTerms :: Parser [Term]
pTerms = do
  void $ PR.symbol "Com_"
  n <- PR.nat
  PR.parens (PR.count n pTerm)
  PR.<?> "terms"

-- poly binop poly (binop: =, >=)
pAtom :: Parser Atom
pAtom = do
  p1 <- pPoly
  op <- PR.choice bin
  p2 <- pPoly
  return $ p1 `op` p2
  PR.<?> "atom"
  where bin = [PR.reserved "=" *> return Eq, PR.reserved ">=" *> return Gte]

-- :|: a1 && a2 && ..
pConstraint :: Parser Constraint
pConstraint = do
  void $ PR.try (PR.symbol underSym)
  pAtom `PR.sepBy` PR.symbol andSym
  PR.<|> return []

pRule :: Parser Rule
pRule = (Rule <$> pTerm <*> (pSep *> pTerms) <*> pConstraint) PR.<?> "rule"

-- TODO: what happens if we have multiple startterms?
-- we could always provide a unique one
pProblem :: Parser [Rule]
pProblem = do
  void $ PR.parens (PR.symbol "GOAL COMPLEXITY")
  void $ PR.parens (PR.symbol "STARTTERM" >> PR.parens (PR.symbol "FUNCTIONSYMBOLS" >> PR.many1 PR.identifier))
  void $ PR.parens (PR.symbol "VAR" >> PR.many PR.identifier)
  PR.parens (PR.symbol "RULES" >> PR.many pRule)
  PR.<?> "problem"

fromString :: String -> [Rule]
fromString s = case PR.parse pProblem "" s of
  Left e   -> error (show e)
  Right rs -> rs

io :: String -> IO ()
io s = do 
  st <- readFile s
  print st
  print $ ppRules (fromString st)

