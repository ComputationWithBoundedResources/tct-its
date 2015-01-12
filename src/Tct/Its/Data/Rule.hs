module Tct.Its.Data.Rule 
  (
  Term (..)
  , Var
  , Fun
  , interpretTerm

  , Atom  (..)
  , Constraint    
  , isLinear
  , filterLinear
  , toGte
  , celems

  , Rule (..)
  , Rules
  , Vars

  , chain

  -- TODO: move
  , ppSep
  , Parser
  , pRule
  ) where


import qualified Data.Set as S
import qualified Data.Map.Strict as M
import Control.Monad (void)
import Control.Applicative
import qualified Text.Parsec.Expr as PE

import qualified Tct.Common.Polynomial as P
import Tct.Common.Ring
import qualified Tct.Core.Common.Pretty as PP
import qualified Tct.Core.Common.Parser as PR

import Tct.Its.Data.Types

isLinearA :: Atom -> Bool
isLinearA (Eq p1 p2)  = P.isLinear p1 && P.isLinear p2
isLinearA (Gte p1 p2) = P.isLinear p1 && P.isLinear p2

toGteA :: Atom -> [Atom]
toGteA (Eq p1 p2)  = [Gte (p1 `sub` p2) zero, Gte (p2 `sub` p1) zero]
toGteA (Gte p1 p2) = [Gte (p1 `sub` p2) zero]

interpretTerm :: (Fun -> [a] -> a) -> (IPoly -> a) -> Term -> a
interpretTerm f g t = f (fun t) (map g (args t))

mapTerm :: (Fun -> Fun) -> (IPoly -> IPoly) -> Term -> Term
mapTerm f g (Term fs as) = Term (f fs) (map g as)

foldTerm :: (a -> IPoly -> a) -> a -> Term -> a
foldTerm f a (Term _ as) = foldl f a as


isLinear :: Constraint -> Bool
isLinear = all isLinearA

filterLinear :: Constraint -> Constraint
filterLinear = filter isLinearA

toGte :: Constraint -> Constraint
toGte = concatMap toGteA

celems :: Constraint -> [IPoly]
celems = concatMap k
  where
    k (Eq e1 e2)  = [e1,e2]
    k (Gte e1 e2) = [e1,e2]

mapRule :: (IPoly -> IPoly) -> Rule -> Rule
mapRule f (Rule l r cs) = Rule (mapTerm id f l) (map (mapTerm id f) r) (map k cs)
  where
    k (Eq p1 p2)  = Eq (f p1) (f p2)
    k (Gte p1 p2) = Gte (f p1) (f p2)

foldRule :: (a -> IPoly -> a) -> a -> Rule -> a
foldRule f a (Rule l r cs) = cfold $ rfold $ lfold a
  where
    lfold b = foldTerm f b l
    rfold b = foldl (foldTerm f) b r
    cfold b = foldl f b (celems cs)

-- | @rename r1 r2@ renames rule @r2@ wrt to rule @r1@.
rename :: Rule -> Rule -> Rule
rename r1 r2 = rename' (renamer r2)
  where
    renamer = mapRule (P.rename (++ "$"))
    r1vars = variables r1
    rename' r
      | S.null (variables r `S.intersection` r1vars) = r
      | otherwise                               = rename' (renamer r)

variables :: Rule -> S.Set Var
variables = foldRule (\acc r -> acc `S.union` S.fromList (P.variables r)) S.empty


-- | @match r1 r2@ matches the rhs of @r1@ with the lhs of @l2@.
chain :: Rule -> Rule -> Maybe Rule
chain ru1 ru2 
  | length (rhs ru1) /= 1 = Nothing
  | otherwise = Just $ chain' ru1 (rename ru1 ru2)
  where
    chain' (Rule l1 r1 cs1) x@(Rule l2 r2 cs2) = Rule 
      { lhs = l1
      , rhs = map (mapTerm id k) r2
      , con = cs1 ++ map (mapCon k) cs2 } 
      where 
        lhsvs = concatMap P.variables (args l2)
        subst1 = M.fromList (map (\v -> (v, P.variable v)) (S.toList $ variables x))
        subst2 = foldl (\m (v,p) -> M.insert v p m) subst1 (zip lhsvs (args (head r1)))
        k = (`P.substituteVariables` subst2) 
        mapCon f (Eq p1 p2)  = Eq (f p1) (f p2)
        mapCon f (Gte p1 p2) = Gte (f p1) (f p2)
  


-- Pretty Printing ---------------------------------------------------------------------------------------------------
arrowSym, underSym, andSym :: String
arrowSym = "->"
underSym = ":|:"
andSym   = "&&"


ppTerm :: Term -> PP.Doc
ppTerm (Term f ts) = PP.string f PP.<> PP.tupled (map PP.pretty ts)

ppTerms ::  [Term] -> PP.Doc
ppTerms [t] = ppTerm t
ppTerms ts  = PP.char 'c' PP.<> PP.int (length ts) PP.<> PP.tupled (map ppTerm ts)

instance PP.Pretty Term where
  pretty = ppTerm

instance PP.Pretty [Term] where
  pretty = ppTerms


ppBinop :: (PP.Pretty a1, PP.Pretty a2) => a1 -> String -> a2 -> PP.Doc
ppBinop t1 op t2 = PP.pretty t1 PP.<+> PP.text op PP.<+> PP.pretty t2

ppAtoms :: [Atom] -> PP.Doc
ppAtoms [] = PP.text "True"
ppAtoms as = PP.encloseSep PP.lbracket PP.rbracket (PP.enclose PP.space PP.space (PP.text andSym)) (map PP.pretty as)

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

pVar :: Parser IPoly
pVar = P.variable <$> PR.identifier

pNat :: Parser IPoly
pNat = P.constant <$> PR.nat

pSep :: Parser ()
pSep = void (PR.symbol "->")

-- constructs a polynomial over an arbitrary arithmetic expression over: int, var, *, +, -, ()
pPoly :: Parser IPoly
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
  void PR.nat
  PR.parens(pTerm `PR.sepBy1` PR.symbol ",")
  PR.<?> "terms"

-- poly binop poly (binop: =, >=)
pAtom :: Parser Atom
pAtom = do
  p1 <- pPoly
  op <- PR.choice bin
  p2 <- pPoly
  return $ p1 `op` p2
  PR.<?> "atom"
  where 
    bin = 
      [ PR.reserved "=" *> return Eq
      , PR.reserved ">=" *> return Gte
      , PR.reserved "=<" *> return (flip Gte)
      , PR.reserved "<=" *> return (flip Gte)
      , PR.reserved ">" *> return (\p1 p2 -> Gte (p1 `sub` one)  p2)
      , PR.reserved "<" *> return (\p2 p1 -> Gte (p1 `sub` one)  p2) ]

-- :|: a1 && a2 && ..
pConstraint :: Parser Constraint
pConstraint = do
  void $ PR.try (PR.symbol underSym)
  pAtom `PR.sepBy` PR.symbol andSym
  PR.<|> return []

pRule :: Parser Rule
pRule = (Rule <$> pTerm <*> (pSep *> (pTerms <|> (:[]) <$> pTerm)) <*> pConstraint) PR.<?> "rule"

