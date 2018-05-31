{-#LANGUAGE  FlexibleContexts,  FlexibleInstances, MultiParamTypeClasses #-}
module Carnap.Languages.PureFirstOrder.Logic.Goldfarb where

import Text.Parsec
import Control.Lens (view)
import Carnap.Core.Data.AbstractSyntaxDataTypes (Form,Term)
import Carnap.Core.Data.AbstractSyntaxClasses (lhs)
import Carnap.Languages.Util.LanguageClasses
import Carnap.Languages.Util.GenericParsers
import Carnap.Languages.PureFirstOrder.Syntax (PureLanguageFOL, PureLexiconFOL,fogamma)
import Carnap.Languages.PureFirstOrder.Parser
import qualified Carnap.Languages.PurePropositional.Logic.Rules as P
import Carnap.Languages.ClassicalSequent.Syntax
import Carnap.Calculi.NaturalDeduction.Syntax
import Carnap.Calculi.NaturalDeduction.Parser (toDeductionLemmon,toDeductionLemmonAlt)
import Carnap.Calculi.NaturalDeduction.Checker (hoProcessLineLemmonMemo, hoProcessLineLemmon)
import Carnap.Languages.PureFirstOrder.Logic.Rules

------------------------------------
--  1. The basic Goldfarb system  --
------------------------------------

data GoldfarbND = TF Int | P | D | UI | UG | CQ1 | CQ2
                  deriving Eq

instance Show GoldfarbND where
        show (TF _)   = "TF"
        show UG       = "UG"
        show P        = "P"
        show D        = "D"
        show UI       = "UI"
        show CQ1      = "CQ"
        show CQ2      = "CQ"

instance Inference GoldfarbND PureLexiconFOL (Form Bool) where

    ruleOf UI = universalInstantiation
    ruleOf UG = universalGeneralization
    ruleOf P = P.axiom
    ruleOf D = P.explicitConditionalProofVariations !! 0
    ruleOf CQ1 = quantifierNegation !! 0
    ruleOf CQ2 = quantifierNegation !! 3
    ruleOf (TF n) = P.explosion n

    restriction (TF n) = Just $ tautologicalConstraint 
                                  (map (\m -> phin m :: FOLSequentCalc (Form Bool)) [1 .. n])
                                  (phin (n + 1) :: FOLSequentCalc (Form Bool))
    restriction UG = Just (eigenConstraint (SeqT 1) (SS (lall "v" $ phi' 1)) (fogamma 1))
    restriction _ = Nothing

    globalRestriction (Left ded) n D = Just (P.dischargeConstraint n ded (view lhs $ conclusionOf D))
    globalRestriction _ _ _ = Nothing

    isAssumption P = True
    isAssumption _ = False

parseGoldfarbND rtc n _ = do r <- choice (map (try . string) ["P","D","CQ","UI","TF","UG"])
                             case r of 
                                  r | r == "P" -> return [P]
                                    | r == "D" -> return [D]
                                    | r == "CQ" -> return [CQ1,CQ2]
                                    | r == "UI" -> return [UI]
                                    | r == "UG" -> return [UG]
                                    | r == "TF" -> return [TF n]

parseGoldfarbNDProof ::  RuntimeNaturalDeductionConfig PureLexiconFOL (Form Bool) -> String -> [DeductionLine GoldfarbND PureLexiconFOL (Form Bool)]
parseGoldfarbNDProof ders = toDeductionLemmon (parseGoldfarbND ders) goldfarbNDFormulaParser

parseGoldfarbAltNDProof ::  RuntimeNaturalDeductionConfig PureLexiconFOL (Form Bool) -> String -> [DeductionLine GoldfarbND PureLexiconFOL (Form Bool)]
parseGoldfarbAltNDProof ders = toDeductionLemmonAlt (parseGoldfarbND ders) goldfarbNDFormulaParser

goldfarbNDCalc = NaturalDeductionCalc
    { ndRenderer = LemmonStyle
    , ndParseProof = parseGoldfarbNDProof
    , ndProcessLine = hoProcessLineLemmon
    , ndProcessLineMemo = Just hoProcessLineLemmonMemo
    , ndParseSeq = folSeqParser
    }

goldfarbAltNDCalc = goldfarbNDCalc { ndParseProof = parseGoldfarbAltNDProof }

------------------------------------------------------------------------
--  2. The system with convenience rules for existential quantifiers  --
------------------------------------------------------------------------

data GoldfarbNDPlus = ND GoldfarbND | EG | EII String | EIE
                        deriving Eq

instance Show GoldfarbNDPlus where
        show (ND s) = show s
        show EG = "EG"
        show (EII v) = "EII(" ++ v ++ ")" 
        show EIE = "EIE"
        --XXX: including v is important, since the memoization relies
        --hashing the rule, which relies on its show instance

instance Inference GoldfarbNDPlus PureLexiconFOL (Form Bool) where

    ruleOf (ND s) = ruleOf s
    ruleOf EG = existentialGeneralization
    ruleOf (EII _) = existentialAssumption
    ruleOf EIE = existentialAssumptionDischarge

    restriction (ND s) = restriction s
    restriction _ = Nothing

    globalRestriction (Left ded) n (ND D) = Just (P.dischargeConstraint n ded (view lhs $ conclusionOf (ND D)))
    globalRestriction (Left ded) n (EII v) = case parse (parseFreeVar ['a'..'z'] :: Parsec String u (PureLanguageFOL (Term Int))) "" v  of
                                                 Left e -> Just (const $ Just "couldn't parse flagged term")
                                                 Right v' -> Just (totallyFreshConstraint n ded (taun 1) v')
    globalRestriction (Left ded) n EIE = Just (P.dischargeConstraint n ded (view lhs $ conclusionOf EIE)
                                              `andFurtherRestriction` flaggedVariableConstraint n ded theSuc checkEII)
        where checkEII (EII v) = case parse (parseFreeVar ['a'..'z'] :: Parsec String u (PureLanguageFOL (Term Int))) "" v of
                                     Right v' -> Right (liftToSequent v')
                                     Left e -> Left "couldn't parse flagged term"
              checkEII _ = Left "The discharged premise is not justified with EII"
              theSuc = SS (phin 1 :: FOLSequentCalc (Form Bool))

    globalRestriction _ _ _ = Nothing

    isAssumption (ND s)  = isAssumption s
    isAssumption (EII _) = True
    isAssumption _ = False

parseGoldfarbNDPlus rtc n annote = plusRules <|> (map ND <$> parseGoldfarbND rtc n annote)
            where plusRules = do r <- choice (map (try . string) ["EG","EII","EIE"])
                                 case r of 
                                        r | r == "EG" -> return [EG]
                                          | r == "EII" -> return [EII annote]
                                          | r == "EIE" -> return [EIE]

parseGoldfarbNDPlusProof ::  RuntimeNaturalDeductionConfig PureLexiconFOL (Form Bool) -> String -> [DeductionLine GoldfarbNDPlus PureLexiconFOL (Form Bool)]
parseGoldfarbNDPlusProof rtc = toDeductionLemmon (parseGoldfarbNDPlus rtc) goldfarbNDFormulaParser

parseGoldfarbAltNDPlusProof ::  RuntimeNaturalDeductionConfig PureLexiconFOL (Form Bool) -> String -> [DeductionLine GoldfarbNDPlus PureLexiconFOL (Form Bool)]
parseGoldfarbAltNDPlusProof rtc = toDeductionLemmonAlt (parseGoldfarbNDPlus rtc) goldfarbNDFormulaParser

goldfarbNDPlusCalc = NaturalDeductionCalc
    { ndRenderer = LemmonStyle
    , ndParseProof = parseGoldfarbNDPlusProof
    , ndProcessLine = hoProcessLineLemmon
    , ndProcessLineMemo = Just hoProcessLineLemmonMemo
    , ndParseSeq = folSeqParser
    }

goldfarbAltNDPlusCalc = goldfarbNDPlusCalc { ndParseProof = parseGoldfarbAltNDPlusProof }
