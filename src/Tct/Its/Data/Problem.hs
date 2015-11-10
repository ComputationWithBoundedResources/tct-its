module Tct.Its.Data.Problem
  ( Its (..)
  , ItsStrategy
  , ItsDeclaration

  , initialise
  , removeRules
  , restrictRules

  , validate

  --, rvss
  , domain
  , sizeIsDefined
  , isClosed
  , closedProof
  , updateTimebounds
  , startrules

  , Progress (..)
  , hasProgress
  , progress
  ) where


import qualified Data.IntMap.Strict               as IM
import qualified Data.Map.Strict                  as M
import           Data.Maybe                       (isJust)
import           Data.Typeable

import qualified Tct.Core.Common.Pretty           as PP
import qualified Tct.Core.Common.Xml              as Xml
import qualified Tct.Core.Data                    as T

import qualified Tct.Common.Polynomial            as P
import           Tct.Common.ProofCombinators

import           Tct.Its.Data.Complexity          (toComplexity)
import           Tct.Its.Data.LocalSizebounds     (LocalSizebounds)
import           Tct.Its.Data.ResultVariableGraph (RVGraph)
import           Tct.Its.Data.Rule
import           Tct.Its.Data.Sizebounds          (Sizebounds)
import           Tct.Its.Data.Timebounds          (Timebounds)
import qualified Tct.Its.Data.Timebounds          as TB
import           Tct.Its.Data.TransitionGraph     (TGraph)
import qualified Tct.Its.Data.TransitionGraph     as TG
import           Tct.Its.Data.Types


data Its = Its
  { irules_          :: Rules
  , signature_       :: Signature
  , startterm_       :: Term

  , tgraph_          :: TGraph
  , rvgraph_         :: Maybe RVGraph

  , timebounds_      :: Timebounds
  , sizebounds_      :: Maybe Sizebounds
  , localSizebounds_ :: Maybe LocalSizebounds
  } deriving (Show, Typeable)

type ItsStrategy    = T.Strategy Its Its
type ItsDeclaration = T.StrategyDeclaration Its Its

sizeIsDefined :: Its -> Bool
sizeIsDefined prob = isJust (rvgraph_ prob) && isJust (sizebounds_ prob) && isJust (localSizebounds_ prob)


initialise :: ([Fun], [Var], [Rule]) -> Its
initialise ([fs],_, rsl) = Its
  { irules_          = allRules
  , signature_       = mkSignature

  , startterm_       = Term fs (args $ lhs start)

  , tgraph_          = tgraph
  , rvgraph_         = Nothing

  , timebounds_      = TB.initialise (IM.keys allRules) (IM.keys startRules)
  , sizebounds_      = Nothing
  , localSizebounds_ = Nothing }
  where
    allRules   = IM.fromList $ zip [0..] rsl
    startRules = IM.filter (\r -> fun (lhs r) == fs) allRules
    start      = snd $ IM.findMin startRules
    tgraph = TG.estimateGraph allRules
    mkSignature = foldl M.union M.empty $ map k [ lhs r : rhs r | r <- rsl ]
      where k = foldl (\m t -> M.insert (fun t) (length $ args t) m) M.empty
initialise _ = error "Problem.initialise: not implemented: multiple start symbols"

startrules :: Its -> Rules
startrules prob = IM.filter (\r -> fun (lhs r) == fs) (irules_ prob)
  where Term fs _ = startterm_ prob


validate :: Its -> Bool
validate prob = all validRule $ IM.elems (irules_ prob)
  where
    validRule ru = case rhs ru of
      [r] -> all P.isLinear (args r)
      _   -> False

removeRules :: [RuleId] -> Its -> Its
removeRules irs prob = prob
  { irules_          = IM.filterWithKey (\k _ -> k `notElem` irs) (irules_ prob)
  , tgraph_          = TG.deleteNodes irs (tgraph_ prob)
  -- MS: TODO filter wrt to labels
  , rvgraph_         = Nothing
  , timebounds_      = TB.filterRules (`notElem` irs) (timebounds_ prob)
  , sizebounds_      = M.filterWithKey (\rv _ -> rvRule rv `notElem` irs) `fmap` sizebounds_ prob
  , localSizebounds_ = M.filterWithKey (\rv _ -> rvRule rv `notElem` irs) `fmap` localSizebounds_ prob }

restrictRules :: [RuleId] -> Its -> Its
restrictRules irs prob = prob
  { irules_          = IM.filterWithKey (\k _ -> k `elem` irs) (irules_ prob)
  , tgraph_          = TG.restrictToNodes irs (tgraph_ prob)
  -- MS: TODO restrict to labels
  , rvgraph_         = Nothing
  , timebounds_      = TB.filterRules (`elem` irs) (timebounds_ prob)
  , sizebounds_      = M.filterWithKey (\rv _ -> rvRule rv `elem` irs) `fmap` sizebounds_ prob
  , localSizebounds_ = M.filterWithKey (\rv _ -> rvRule rv `elem` irs) `fmap` localSizebounds_ prob }

{-rvss :: Vars -> Rules -> [RV]-}
{-rvss vs = concatMap k-}
  {-where k (i,r) = [ (i, rhsIdx, v) | rhsIdx <- [1..length (rhs r)], v <- vs ]-}

-- | returns the domain; which is fixed for a problem
domain :: Its -> Vars
domain = concatMap P.variables . args . startterm_


isClosed :: Its -> Bool
isClosed = TB.allDefined . timebounds_


data Progress a = Progress a | NoProgress

cert :: T.Optional T.Id T.Certificate -> T.Certificate
cert T.Null           = T.timeUBCert T.constant
cert (T.Opt (T.Id c)) = c

progress :: (T.Processor p, T.Forking p ~ T.Optional T.Id) => Progress (T.Out p) -> T.ProofObject p -> T.TctM (T.Return p)
progress (Progress prob') proof = T.succeedWith proof cert (T.Opt $ T.Id prob')
progress NoProgress proof       = T.abortWith proof

closedProof :: (T.Processor p, T.Forking p ~ T.Optional a, T.ProofObject p ~ ApplicationProof p1) => Its -> T.TctM (T.Return p)
closedProof prob = T.succeedWith Closed (const $ T.timeUBCert b) T.Null
  where b = toComplexity $ TB.totalBound (timebounds_ prob)

ppRules :: Rules -> TB.Timebounds -> PP.Doc
ppRules rs tb =
  PP.table
    [ (PP.AlignLeft, map (\i -> PP.int i PP.<> PP.dot PP.<> PP.space) is)
    , (PP.AlignLeft, lhss)
    , (PP.AlignLeft, rhss)
    , (PP.AlignLeft, css)
    , (PP.AlignLeft, tbs)]
  where
    lhss = map (PP.pretty . lhs) rsl
    rhss = map ((\p -> PP.space PP.<> ppSep PP.<+> p PP.<> PP.space) . PP.pretty . rhs ) rsl
    css  = map (PP.pretty . con ) rsl
    tbs  = map (\x -> (PP.space PP.<>) $ PP.tupled [PP.pretty $ tb `TB.tboundOf` x, PP.pretty $ tb `TB.tcostOf` x]) is
    (is, rsl) = unzip (IM.assocs rs)


hasProgress :: Its -> TB.TimeboundsMap -> Bool
hasProgress prob = TB.hasProgress (timebounds_ prob)

updateTimebounds :: Its -> TB.TimeboundsMap -> Its
updateTimebounds prob tb = prob { timebounds_ = TB.updates (timebounds_ prob) tb }

instance PP.Pretty Its where
  pretty prob =
    pp "Rules:" (ppRules (irules_ prob) (timebounds_ prob))
    PP.<$$> pp "Signature:" (PP.pretty $ signature_ prob)
    PP.<$$> pp "Flow Graph:" (PP.pretty (tgraph_ prob))
    --PP.<$$> pp "Sizebounds:" (PP.pretty (sizebounds_ prob))
    where pp st p = PP.text st PP.<$$> PP.indent 2 p

instance Xml.Xml Its where
  toXml _ = Xml.elt "itsInput" []

