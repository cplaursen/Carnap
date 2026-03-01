{-#LANGUAGE RankNTypes, FlexibleContexts #-}

module Main where

import System.Environment (getArgs)
import System.Exit (exitFailure, exitSuccess)
import System.IO (hPutStrLn, stderr)
import Control.Applicative ((<|>))
import Carnap.Calculi.NaturalDeduction.Syntax
    (NaturalDeductionCalc(..), Feedback(..), Inference)
import Carnap.Calculi.NaturalDeduction.Checker (toDisplaySequence)
import Carnap.Calculi.Util
    (ProofErrorMessage(..), defaultRuntimeDeductionConfig)
import Carnap.Languages.PurePropositional.Syntax (PurePropLexicon)
import Carnap.Languages.PurePropositional.Logic (ofPropSys)
import Carnap.Languages.PureFirstOrder.Syntax (PureLexiconFOL)
import Carnap.Languages.PureFirstOrder.Logic (ofFOLSys)
import Carnap.Core.Data.Types (Form(..))
import Data.Char (isSpace)
import Text.Parsec.Error (errorMessages, errorPos, showErrorMessages)
import Text.Parsec.Pos (sourceColumn)

main :: IO ()
main = do
    args <- getArgs
    case args of
        ["--list"] -> printSystems
        [sys, filepath] -> do
            proofText <- readFile filepath
            let result = dispatchProp proofText sys
                     <|> dispatchFOL  proofText sys
            case result of
                Nothing -> do
                    hPutStrLn stderr $ "Unknown system: " ++ sys
                    hPutStrLn stderr "Use --list to see available systems."
                    exitFailure
                Just action -> action
        _ -> do
            hPutStrLn stderr "Usage: carnap-check <system> <file>"
            hPutStrLn stderr "       carnap-check --list"
            exitFailure

dispatchProp :: String -> String -> Maybe (IO ())
dispatchProp proofText = ofPropSys go
    where go :: (Show r, Inference r PurePropLexicon (Form Bool))
             => NaturalDeductionCalc r PurePropLexicon (Form Bool) -> IO ()
          go ndcalc = do
              let pt  = strip proofText
                  ded = ndParseProof ndcalc defaultRuntimeDeductionConfig pt
                  Feedback mseq ds = toDisplaySequence (ndProcessLine ndcalc) ded
              presentResults (show <$> mseq) ds

dispatchFOL :: String -> String -> Maybe (IO ())
dispatchFOL proofText = ofFOLSys go
    where go :: (Show r, Inference r PureLexiconFOL (Form Bool))
             => NaturalDeductionCalc r PureLexiconFOL (Form Bool) -> IO ()
          go ndcalc = do
              let pt  = strip proofText
                  ded = ndParseProof ndcalc defaultRuntimeDeductionConfig pt
                  Feedback mseq ds = toDisplaySequence (ndProcessLine ndcalc) ded
              presentResults (show <$> mseq) ds

strip :: String -> String
strip = reverse . dropWhile isSpace . reverse . dropWhile isSpace

presentResults :: Maybe String -> [Either (ProofErrorMessage lex) b] -> IO ()
presentResults mseq ds = do
    let errors = concatMap reportError (zip [1..] ds)
    if null errors
        then do case mseq of
                    Just s  -> putStrLn $ "Proven: " ++ s
                    Nothing -> putStrLn "Proof valid."
                exitSuccess
        else do mapM_ (hPutStrLn stderr) errors
                case mseq of
                    Nothing -> do
                        hPutStrLn stderr "Proof invalid."
                        exitFailure
                    Just s  -> do
                        putStrLn $ "Proven (with warnings): " ++ s
                        exitSuccess

reportError :: (Int, Either (ProofErrorMessage lex) a) -> [String]
reportError (_, Right _) = []
reportError (_, Left (NoResult _)) = []
reportError (_, Left (NoParse err ln)) =
    ["Line " ++ show ln ++ ", column " ++ show (sourceColumn (errorPos err))
     ++ ": parse error: "
     ++ showErrorMessages "or" "unknown" "expecting" "unexpected" "end of input"
            (errorMessages err)]
reportError (_, Left (NoUnify _ ln)) =
    ["Line " ++ show ln ++ ": could not unify"]
reportError (_, Left (GenericError msg ln)) =
    ["Line " ++ show ln ++ ": " ++ msg]

printSystems :: IO ()
printSystems = do
    putStrLn "Available systems:"
    putStrLn ""
    putStrLn "Propositional logic:"
    mapM_ (putStrLn . ("  " ++)) propSystems
    putStrLn ""
    putStrLn "First-order logic:"
    mapM_ (putStrLn . ("  " ++)) folSystems

propSystems :: [String]
propSystems =
    [ "LogicBookSD", "LogicBookSDPlus"
    , "allenSL", "allenSLPlus"
    , "arthurSL"
    , "belotSD", "belotSDPlus"
    , "bonevacSL"
    , "cortensSL"
    , "davisSL"
    , "ebelsDugganTFL"
    , "fosterAndLaursenTFL", "fosterAndLaursenTFL2019", "fosterAndLaursenTFLCore"
    , "gallowSL", "gallowSLPlus"
    , "gamutIPND", "gamutMPND", "gamutPND", "gamutPNDPlus"
    , "goldfarbPropND"
    , "gregorySD", "gregorySDE"
    , "hardegreeSL", "hardegreeSL2006"
    , "hausmanSL"
    , "howardSnyderSL"
    , "hurleySL"
    , "ichikawaJenkinsSL"
    , "landeProp"
    , "lemmonProp"
    , "magnusSL", "magnusSLPlus"
    , "montagueSC"
    , "prop", "propStrict", "propNonC", "propNL", "propNLStrict"
    , "thomasBolducAndZachTFL", "thomasBolducAndZachTFL2019", "thomasBolducAndZachTFLCore"
    , "tomassiPL"
    , "winklerTFL"
    , "zachPropEq"
    ]

folSystems :: [String]
folSystems =
    [ "LogicBookPD", "LogicBookPDE", "LogicBookPDEPlus", "LogicBookPDPlus"
    , "arthurQL"
    , "belotPD", "belotPDE", "belotPDEPlus", "belotPDPlus"
    , "bonevacQL"
    , "cortensQL"
    , "davisQL"
    , "ebelsDugganFOL"
    , "firstOrder", "firstOrderNonC"
    , "fosterAndLaursenFOL", "fosterAndLaursenFOL2019", "fosterAndLaursenFOLCore", "fosterAndLaursenFOLPlus2019"
    , "gallowPL", "gallowPLPlus"
    , "gamutND", "gamutNDPlus"
    , "goldfarbAltND", "goldfarbAltNDPlus", "goldfarbND", "goldfarbNDPlus"
    , "gregoryPD", "gregoryPDE"
    , "hardegreePL", "hardegreePL2006"
    , "hausmanPL"
    , "howardSnyderPL"
    , "hurleyPL"
    , "ichikawaJenkinsQL"
    , "landeQuant"
    , "lemmonQuant"
    , "magnusQL", "magnusQLPlus"
    , "montagueQC"
    , "thomasBolducAndZachFOL", "thomasBolducAndZachFOL2019"
    , "thomasBolducAndZachFOLCore", "thomasBolducAndZachFOLPlus2019"
    , "tomassiQL"
    , "winklerFOL"
    , "zachFOLEq"
    ]
