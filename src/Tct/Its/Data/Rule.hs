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

type Fun  = String
data Term = Term 
  { fun  :: Fun 
  , args :: [Poly]
  } deriving (Eq, Ord, Show)

data Atom
  = Eq Poly Poly
  | Gte Poly Poly
  deriving (Eq, Ord, Show)

isLinearA :: Atom -> Bool
isLinearA (Eq p1 p2)  = P.isLinear p1 && P.isLinear p2
isLinearA (Gte p1 p2) = P.isLinear p1 && P.isLinear p2

normaliseA :: Atom -> [Atom]
normaliseA (Eq p1 p2)  = [Gte (p1 `sub` p2) zero, Gte (p2 `sub` p1) zero]
normaliseA (Gte p1 p2) = [Gte (p1 `sub` p2) zero]

interpretTerm :: (Fun -> [a] -> a) -> (Poly -> a) -> Term -> a
interpretTerm f g t = f (fun t) (map g (args t))

type Constraint = [Atom]

isLinear :: Constraint -> Bool
isLinear = all isLinearA

normalise :: Constraint -> Constraint
normalise = concatMap normaliseA


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


ppTerm :: Term -> PP.Doc
ppTerm (Term f ts) = PP.string f PP.<> PP.tupled (map PP.pretty ts)

ppTerms ::  [Term] -> PP.Doc
ppTerms ts = PP.char 'c' PP.<> PP.int (length ts) PP.<> PP.tupled (map PP.pretty ts)

instance PP.Pretty Term where
  pretty = ppTerm

instance PP.Pretty [Term] where
  pretty = ppTerms


ppBinop :: (PP.Pretty a1, PP.Pretty a2) => a1 -> String -> a2 -> PP.Doc
ppBinop t1 op t2 = PP.pretty t1 PP.<+> PP.text op PP.<+> PP.pretty t2

ppAtoms :: [Atom] -> PP.Doc
ppAtoms [] = PP.text "True"
ppAtoms as = PP.encloseSep PP.lbracket PP.rbracket (PP.text andSym) (map PP.pretty as)

instance PP.Pretty Atom where
  pretty (Eq t1 t2)  = ppBinop t1 "=" t2
  pretty (Gte t1 t2) = ppBinop t1 ">=" t2

instance PP.Pretty [Atom] where
  pretty = ppAtoms


ppSep :: PP.Doc
ppSep = PP.text arrowSym

instance PP.Pretty Rule where
  pretty (Rule l rs cs) =
    PP.pretty l PP.<+> ppSep PP.<+> ppTerms rs PP.<+> ppAtoms cs

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
    unary f op = PE.Prefix (PR.reserved f *> return op)
    binaryL f op = PE.Infix (PR.reserved f *> return op)

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

