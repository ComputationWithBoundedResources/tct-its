module Tct.Its.Data.Problem
  ( Its (..)
  , ItsStrategy

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
  { _irules          :: Rules
  , _signature       :: Signature
  , _startterm       :: Term

  , _tgraph          :: TGraph
  , _rvgraph         :: Maybe RVGraph

  , _timebounds      :: Timebounds
  , _sizebounds      :: Maybe Sizebounds
  , _localSizebounds :: Maybe LocalSizebounds
  } deriving (Show, Typeable)

type ItsStrategy = T.Strategy Its Its

sizeIsDefined :: Its -> Bool
sizeIsDefined prob = isJust (_rvgraph prob) && isJust (_sizebounds prob) && isJust (_localSizebounds prob)


initialise :: ([Fun], [Var], [Rule]) -> Its
initialise ([fs],_, rsl) = Its
  { _irules          = allRules
  , _signature       = mkSignature

  , _startterm       = Term fs (args $ lhs start)

  , _tgraph          = tgraph
  , _rvgraph         = Nothing

  , _timebounds      = TB.initialise (IM.keys allRules) (IM.keys startRules)
  , _sizebounds      = Nothing
  , _localSizebounds = Nothing }
  where
    allRules   = IM.fromList $ zip [0..] rsl
    startRules = IM.filter (\r -> fun (lhs r) == fs) allRules
    start      = snd $ IM.findMin startRules
    tgraph = TG.estimateGraph allRules
    mkSignature = foldl M.union M.empty $ map k [ lhs r : rhs r | r <- rsl ]
      where k = foldl (\m t -> M.insert (fun t) (length $ args t) m) M.empty
initialise _ = error "Problem.initialise: not implemented: multiple start symbols"

startrules :: Its -> Rules
startrules prob = IM.filter (\r -> fun (lhs r) == fs) (_irules prob)
  where Term fs _ = _startterm prob


validate :: Its -> Bool
validate prob = all validRule $ IM.elems (_irules prob)
  where
    validRule ru = case rhs ru of
      [r] -> all P.isLinear (args r)
      _   -> False

removeRules :: [RuleId] -> Its -> Its
removeRules irs prob = prob
  { _irules          = IM.filterWithKey (\k _ -> k `notElem` irs) (_irules prob)
  , _tgraph          = TG.deleteNodes irs (_tgraph prob)
  -- MS: TODO filter wrt to labels
  , _rvgraph         = Nothing
  , _timebounds      = TB.filterRules (`notElem` irs) (_timebounds prob)
  , _sizebounds      = M.filterWithKey (\rv _ -> rvRule rv `notElem` irs) `fmap` _sizebounds prob
  , _localSizebounds = M.filterWithKey (\rv _ -> rvRule rv `notElem` irs) `fmap` _localSizebounds prob }

restrictRules :: [RuleId] -> Its -> Its
restrictRules irs prob = prob
  { _irules          = IM.filterWithKey (\k _ -> k `elem` irs) (_irules prob)
  , _tgraph          = TG.restrictToNodes irs (_tgraph prob)
  -- MS: TODO restrict to labels
  , _rvgraph         = Nothing
  , _timebounds      = TB.filterRules (`elem` irs) (_timebounds prob)
  , _sizebounds      = M.filterWithKey (\rv _ -> rvRule rv `elem` irs) `fmap` _sizebounds prob
  , _localSizebounds = M.filterWithKey (\rv _ -> rvRule rv `elem` irs) `fmap` _localSizebounds prob }

{-rvss :: Vars -> Rules -> [RV]-}
{-rvss vs = concatMap k-}
  {-where k (i,r) = [ (i, rhsIdx, v) | rhsIdx <- [1..length (rhs r)], v <- vs ]-}

-- | returns the domain; which is fixed for a problem
domain :: Its -> Vars
domain = concatMap P.variables . args . _startterm


isClosed :: Its -> Bool
isClosed = TB.allDefined . _timebounds


data Progress a = Progress a | NoProgress

cert :: T.Optional T.Id T.Certificate -> T.Certificate
cert T.Null           = T.timeUBCert T.constant
cert (T.Opt (T.Id c)) = c

progress :: (T.Processor p, T.Forking p ~ T.Optional T.Id) => Progress (T.Out p) -> T.ProofObject p -> T.TctM (T.Return p)
progress (Progress prob') proof = T.succeedWith proof cert (T.Opt $ T.Id prob')
progress NoProgress proof       = T.abortWith proof

closedProof :: (T.Processor p, T.Forking p ~ T.Optional a, T.ProofObject p ~ ApplicationProof p1) => Its -> T.TctM (T.Return p)
closedProof prob = T.succeedWith Closed (const $ T.timeUBCert b) T.Null
  where b = toComplexity $ TB.totalBound (_timebounds prob)

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
hasProgress prob = TB.hasProgress (_timebounds prob)

updateTimebounds :: Its -> TB.TimeboundsMap -> Its
updateTimebounds prob tb = prob { _timebounds = TB.updates (_timebounds prob) tb }

instance PP.Pretty Its where
  pretty prob =
    pp "Rules:" (ppRules (_irules prob) (_timebounds prob))
    PP.<$$> pp "Signature:" (PP.pretty $ _signature prob)
    PP.<$$> pp "Flow Graph:" (PP.pretty (_tgraph prob))
    --PP.<$$> pp "Sizebounds:" (PP.pretty (_sizebounds prob))
    where pp st p = PP.text st PP.<$$> PP.indent 2 p

instance Xml.Xml Its where
  toXml _ = Xml.elt "itsInput" []

