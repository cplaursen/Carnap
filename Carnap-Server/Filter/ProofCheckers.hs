{-# LANGUAGE OverloadedStrings #-}
module Filter.ProofCheckers (makeProofChecker) where

import Text.Pandoc
import Data.Map (Map, unions, fromList, toList)
import qualified Data.Text as T
import Data.Text (Text)
import Filter.Util (numof, intoChunks, formatChunk, unlines', exerciseWrapper)
import Prelude

makeProofChecker :: Block -> Block
makeProofChecker cb@(CodeBlock (_,classes,extra) contents)
    | "ProofChecker" `elem` classes = Div ("",[],[]) $ map (activate classes extra) $ intoChunks contents
    | "Playground" `elem` classes = Div ("",[],[]) [toPlayground classes extra contents]
    | otherwise = cb
makeProofChecker x = x

activate :: [Text] -> [(Text, Text)] -> Text -> Block
activate cls extra chunk
    | "AllenSL"          `elem` cls = exTemplate [("system", "allenSL")]
    | "AllenSLPlus"      `elem` cls = exTemplate [("system", "allenSLPlus")]
    | "BelotPD"          `elem` cls = exTemplate [("system", "belotPD")]
    | "BelotPDE"         `elem` cls = exTemplate [("system", "belotPDE")]
    | "BelotPDEPlus"     `elem` cls = exTemplate [("system", "belotPDEPlus")]
    | "BelotPDPlus"      `elem` cls = exTemplate [("system", "belotPDPlus")]
    | "BelotSD"          `elem` cls = exTemplate [("system", "belotSD")]
    | "BelotSDPlus"      `elem` cls = exTemplate [("system", "belotSDPlus")]
    | "BonevacQL"        `elem` cls = exTemplate [("system", "bonevacQL"), ("guides", "montague"), ("options", "fonts resize")]
    | "BonevacSL"        `elem` cls = exTemplate [("system", "bonevacSL"), ("guides", "montague"), ("options", "fonts resize")]
    | "EbelsDugganFOL"   `elem` cls = exTemplate [("system", "ebelsDugganFOL"), ("guides", "fitch"), ("options", "fonts resize")]
    | "EbelsDugganTFL"   `elem` cls = exTemplate [("system", "ebelsDugganTFL"), ("guides", "fitch"), ("options", "fonts resize")]
    | "ElementaryST"     `elem` cls = exTemplate [("system", "elementarySetTheory"),("options","resize render")]
    | "FirstOrder"       `elem` cls = exTemplate [("system", "firstOrder"),("guides","montague"),("options","resize")]
    | "ForallxQL"        `elem` cls = exTemplate [("system", "magnusQL"), ("options","render")]
    | "ForallxQLPlus"    `elem` cls = exTemplate [("system", "magnusQLPlus"), ("options","render")]
    | "ForallxSL"        `elem` cls = exTemplate [("system", "magnusSL"), ("options","render")]
    | "ForallxSLPlus"    `elem` cls = exTemplate [("system", "magnusSLPlus"), ("options","render")]
    | "GallowPL"         `elem` cls = exTemplate [("system", "gallowPL"), ("options","render")]
    | "GallowPLPlus"     `elem` cls = exTemplate [("system", "gallowPLPlus"), ("options","render")]
    | "GallowSL"         `elem` cls = exTemplate [("system", "gallowSL"), ("options","render")]
    | "GallowSLPlus"     `elem` cls = exTemplate [("system", "gallowSLPlus"), ("options","render")]
    | "GamutIPND"        `elem` cls = exTemplate [("system", "gamutIPND"), ("guides","hausman"), ("options", "resize fonts") ]
    | "GamutMPND"        `elem` cls = exTemplate [("system", "gamutMPND"), ("guides","hausman"), ("options", "resize fonts") ]
    | "GamutND"          `elem` cls = exTemplate [("system", "gamutND"), ("guides","hausman"), ("options", "resize fonts") ]
    | "GamutNDDesc"      `elem` cls = exTemplate [("system", "gamutNDDesc"), ("guides","hausman"), ("options", "resize fonts") ]
    | "GamutNDPlus"      `elem` cls = exTemplate [("system", "gamutNDPlus"), ("guides","hausman"), ("options", "resize fonts") ]
    | "GamutPND"         `elem` cls = exTemplate [("system", "gamutPND"), ("guides","hausman"), ("options", "resize fonts") ]
    | "GamutPNDPlus"     `elem` cls = exTemplate [("system", "gamutPNDPlus"), ("guides","hausman"), ("options", "resize fonts") ]
    | "GoldfarbAltND"    `elem` cls = exTemplate [("system", "goldfarbAltND")]
    | "GoldfarbAltNDPlus"`elem` cls = exTemplate [("system", "goldfarbAltNDPlus")]
    | "GoldfarbND"       `elem` cls = exTemplate [("system", "goldfarbND")]
    | "GoldfarbNDPlus"   `elem` cls = exTemplate [("system", "goldfarbNDPlus")]
    | "GoldfarbPropND"   `elem` cls = exTemplate [("system", "goldfarbPropND")]
    | "Hardegree4"       `elem` cls = exTemplate [("system", "hardegree4"), ("guides", "montague"), ("options", "fonts")]
    | "Hardegree5"       `elem` cls = exTemplate [("system", "hardegree5"), ("guides", "montague"), ("options", "fonts")]
    | "HardegreeB"       `elem` cls = exTemplate [("system", "hardegreeB"), ("guides", "montague"), ("options", "fonts")]
    | "HardegreeD"       `elem` cls = exTemplate [("system", "hardegreeD"), ("guides", "montague"), ("options", "fonts")]
    | "HardegreeK"       `elem` cls = exTemplate [("system", "hardegreeK"), ("guides", "montague"), ("options", "fonts")]
    | "HardegreeL"       `elem` cls = exTemplate [("system", "hardegreeL"), ("guides", "montague"), ("options", "fonts")]
    | "HardegreeMPL"     `elem` cls = exTemplate [("system", "hardegreeMPL"), ("guides", "montague"), ("options", "fonts")]
    | "HardegreePL"      `elem` cls = exTemplate [("system", "hardegreePL"), ("options", "render")]
    | "HardegreePL2006"  `elem` cls = exTemplate [("system", "hardegreePL2006"), ("options", "render")]
    | "HardegreeSL"      `elem` cls = exTemplate [("system", "hardegreeSL"), ("options", "render")]
    | "HardegreeSL2006"  `elem` cls = exTemplate [("system", "hardegreeSL2006"), ("options", "render")]
    | "HardegreeT"       `elem` cls = exTemplate [("system", "hardegreeT"), ("guides", "montague"),  ("options", "fonts")]
    | "HardegreeWTL"     `elem` cls = exTemplate [("system", "hardegreeWTL"), ("guides", "montague"), ("options", "render fonts")]
    | "HausmanPL"        `elem` cls = exTemplate [("system", "hausmanPL"), ("guides","hausman"), ("options", "resize fonts") ]
    | "HausmanSL"        `elem` cls = exTemplate [("system", "hausmanSL"), ("guides","hausman"), ("options", "resize fonts") ]
    | "HowardSnyderPL"   `elem` cls = exTemplate [("system", "howardSnyderPL"), ("guides","howardSnyder"), ("options", "resize fonts") ]
    | "HowardSnyderSL"   `elem` cls = exTemplate [("system", "howardSnyderSL"), ("guides","howardSnyder"), ("options", "resize fonts") ]
    | "HurleyPL"         `elem` cls = exTemplate [("system", "hurleyPL"), ("guides", "hurley"), ("options", "resize")]
    | "HurleySL"         `elem` cls = exTemplate [("system", "hurleySL"), ("guides", "hurley"), ("options", "resize")]
    | "IchikawaJenkinsQL"`elem` cls = exTemplate [("system", "ichikawaJenkinsQL"), ("options","render")]
    | "IchikawaJenkinsSL"`elem` cls = exTemplate [("system", "ichikawaJenkinsSL"), ("options","render")]
    | "JohnsonSL"        `elem` cls = exTemplate [("system", "johnsonSL")]
    | "JohnsonSLPlus"    `elem` cls = exTemplate [("system", "johnsonSLPlus")]
    | "LogicBookPD"      `elem` cls = exTemplate [("system", "LogicBookPD")]
    | "LogicBookPDE"     `elem` cls = exTemplate [("system", "LogicBookPDE")]
    | "LogicBookPDEPlus" `elem` cls = exTemplate [("system", "LogicBookPDEPlus")]
    | "LogicBookPDPlus"  `elem` cls = exTemplate [("system", "LogicBookPDPlus")]
    | "LogicBookSD"      `elem` cls = exTemplate [("system", "LogicBookSD")]
    | "LogicBookSDPlus"  `elem` cls = exTemplate [("system", "LogicBookSDPlus")]
    | "MontagueQC"       `elem` cls = exTemplate [("system", "montagueQC"),("options","resize")]
    | "MontagueSC"       `elem` cls = exTemplate [("system", "montagueSC"),("options","resize")]
    | "PolySecondOrder"  `elem` cls = exTemplate [("system", "polyadicSecondOrder")]
    | "Prop"             `elem` cls = exTemplate [("system", "prop"),("guides","montague"),("options","resize")]
    | "GregorySD"        `elem` cls = exTemplate [("system", "gregorySD"),("guides","fitch"),("options","indent fonts resize render")]
    | "GregorySDE"       `elem` cls = exTemplate [("system", "gregorySDE"),("guides","fitch"),("options","indent fonts resize render")]
    | "GregoryPD"        `elem` cls = exTemplate [("system", "gregoryPD"),("guides","fitch"),("options","indent fonts resize render")]
    | "GregoryPDE"       `elem` cls = exTemplate [("system", "gregoryPDE"),("guides","fitch"),("options","indent fonts resize render")]
    | "SecondOrder"      `elem` cls = exTemplate [("system", "secondOrder")]
    | "SeparativeST"     `elem` cls = exTemplate [("system", "separativeSetTheory"),("options","resize render")]
    | "TomassiPL"        `elem` cls = exTemplate [("system", "tomassiPL"), ("options","resize render hideNumbering")]
    | "TomassiQL"        `elem` cls = exTemplate [("system", "tomassiQL"), ("options","resize render hideNumbering")]
    | "WinklerFOL"       `elem` cls = exTemplate [("system", "winklerFOL"), ("guides", "fitch"), ("options", "resize")]
    | "WinklerTFL"       `elem` cls = exTemplate [("system", "winklerTFL"), ("guides", "fitch"), ("options", "resize")]
    | "ZachFOL"          `elem` cls = exTemplate [("system", "thomasBolducAndZachFOL"), ("options","render")]
    | "ZachFOL2019"      `elem` cls = exTemplate [("system", "thomasBolducAndZachFOL2019"), ("options","render")]
    | "ZachFOLCore"      `elem` cls = exTemplate [("system", "thomasBolducAndZachFOLCore"), ("options","render")]
    | "ZachFOLEq"        `elem` cls = exTemplate [("system", "zachFOLEq")]
    | "ZachFOLPlus2019"  `elem` cls = exTemplate [("system", "thomasBolducAndZachFOLPlus2019"), ("options","render")]
    | "ZachPropEq"       `elem` cls = exTemplate [("system", "zachPropEq")]
    | "ZachTFL"          `elem` cls = exTemplate [("system", "thomasBolducAndZachTFL"), ("options","render")]
    | "ZachTFL2019"      `elem` cls = exTemplate [("system", "thomasBolducAndZachTFL2019"), ("options","render")]
    | "ZachTFLCore"      `elem` cls = exTemplate [("system", "thomasBolducAndZachTFLCore"), ("options","render")]
    | otherwise = exTemplate []
    where seqof = T.dropWhile (/= ' ')
          (h:t) = formatChunk chunk
          fixed = [("type","proofchecker"),("goal",seqof h),("submission", T.concat ["saveAs:", numof h])]
          exTemplate opts = template (unions [fromList extra, fromList opts, fromList fixed]) (numof h) (unlines' t)

toPlayground :: [Text] -> [(Text, Text)] -> Text -> Block
toPlayground cls extra content
    | "AllenSL"          `elem` cls = playTemplate [("system", "allenSL")]
    | "AllenSLPlus"      `elem` cls = playTemplate [("system", "allenSLPlus")]
    | "BelotPD"          `elem` cls = playTemplate [("system", "belotPD")]
    | "BelotPDE"         `elem` cls = playTemplate [("system", "belotPDE")]
    | "BelotPDEPlus"     `elem` cls = playTemplate [("system", "belotPDEPlus")]
    | "BelotPDPlus"      `elem` cls = playTemplate [("system", "belotPDPlus")]
    | "BelotSD"          `elem` cls = playTemplate [("system", "belotSD")]
    | "BelotSDPlus"      `elem` cls = playTemplate [("system", "belotSDPlus")]
    | "BonevacQL"        `elem` cls = playTemplate [("system", "bonevacQL"), ("guides", "montague"), ("options", "fonts resize")]
    | "BonevacSL"        `elem` cls = playTemplate [("system", "bonevacSL"), ("guides", "montague"), ("options", "fonts resize")]
    | "EbelsDugganFOL"   `elem` cls = playTemplate [("system", "ebelsDugganFOL"), ("guides", "fitch"), ("options", "fonts resize")]
    | "EbelsDugganTFL"   `elem` cls = playTemplate [("system", "ebelsDugganTFL"), ("guides", "fitch"), ("options", "fonts resize")]
    | "ElementaryST"     `elem` cls = playTemplate [("system", "elementarySetTheory"), ("options","resize render")]
    | "FirstOrder"       `elem` cls = playTemplate [("system", "firstOrder")]
    | "ForallxQL"        `elem` cls = playTemplate [("system", "magnusQL"), ("options","render")]
    | "ForallxQLPlus"    `elem` cls = playTemplate [("system", "magnusQLPlus"), ("options","render")]
    | "ForallxSL"        `elem` cls = playTemplate [("system", "magnusSL"), ("options","render")]
    | "ForallxSLPlus"    `elem` cls = playTemplate [("system", "magnusSLPlus"), ("options","render")]
    | "GallowPL"         `elem` cls = playTemplate [("system", "gallowPL"), ("options","render")]
    | "GallowPLPlus"     `elem` cls = playTemplate [("system", "gallowPLPlus"), ("options","render")]
    | "GallowSL"         `elem` cls = playTemplate [("system", "gallowSL"), ("options","render")]
    | "GallowSLPlus"     `elem` cls = playTemplate [("system", "gallowSLPlus"), ("options","render")]
    | "GamutIPND"        `elem` cls = playTemplate [("system", "gamutIPND"), ("guides","hausman"), ("options", "resize fonts") ]
    | "GamutMPND"        `elem` cls = playTemplate [("system", "gamutMPND"), ("guides","hausman"), ("options", "resize fonts") ]
    | "GamutND"          `elem` cls = playTemplate [("system", "gamutND"), ("guides","hausman"), ("options", "resize fonts") ]
    | "GamutNDDesc"      `elem` cls = playTemplate [("system", "gamutNDDesc"), ("guides","hausman"), ("options", "resize fonts") ]
    | "GamutNDPlus"      `elem` cls = playTemplate [("system", "gamutNDPlus"), ("guides","hausman"), ("options", "resize fonts") ]
    | "GamutPND"         `elem` cls = playTemplate [("system", "gamutPND"), ("guides","hausman"), ("options", "resize fonts") ]
    | "GamutPNDPlus"     `elem` cls = playTemplate [("system", "gamutPNDPlus"), ("guides","hausman"), ("options", "resize fonts") ]
    | "GoldfarbAltND"    `elem` cls = playTemplate [("system", "goldfarbAltND"),("options","resize")]
    | "GoldfarbAltNDPlus"`elem` cls = playTemplate [("system", "goldfarbAltNDPlus"),("options","resize")]
    | "GoldfarbND"       `elem` cls = playTemplate [("system", "goldfarbND"),("options","resize")]
    | "GoldfarbNDPlus"   `elem` cls = playTemplate [("system", "goldfarbNDPlus"),("options","resize")]
    | "GoldfarbPropND"   `elem` cls = playTemplate [("system", "goldfarbPropND"),("options","resize")]
    | "Hardegree4"       `elem` cls = playTemplate [("system", "hardegree4"), ("guides", "montague"), ("options", "fonts")]
    | "Hardegree5"       `elem` cls = playTemplate [("system", "hardegree5"), ("guides", "montague"), ("options", "fonts")]
    | "HardegreeB"       `elem` cls = playTemplate [("system", "hardegreeB"), ("guides", "montague"), ("options", "fonts")]
    | "HardegreeD"       `elem` cls = playTemplate [("system", "hardegreeD"), ("guides", "montague"), ("options", "fonts")]
    | "HardegreeK"       `elem` cls = playTemplate [("system", "hardegreeK"), ("guides", "montague"), ("options", "fonts")]
    | "HardegreeL"       `elem` cls = playTemplate [("system", "hardegreeL"), ("guides", "montague"), ("options", "fonts")]
    | "HardegreeMPL"     `elem` cls = playTemplate [("system", "hardegreeMPL"), ("guides", "montague"), ("options", "fonts")]
    | "HardegreePL"      `elem` cls = playTemplate [("system", "hardegreePL"), ("options", "render")]
    | "HardegreePL2006"  `elem` cls = playTemplate [("system", "hardegreePL2006"), ("options", "render")]
    | "HardegreeSL"      `elem` cls = playTemplate [("system", "hardegreeSL"), ("options", "render")]
    | "HardegreeSL2006"  `elem` cls = playTemplate [("system", "hardegreeSL2006"), ("options", "render")]
    | "HardegreeT"       `elem` cls = playTemplate [("system", "hardegreeT"), ("guides", "montague"), ("options", "fonts")]
    | "HardegreeWTL"     `elem` cls = playTemplate [("system", "hardegreeWTL"), ("guides", "montague"), ("options", "render fonts")]
    | "HausmanPL"        `elem` cls = playTemplate [("system", "hausmanPL"), ("guides","hausman"), ("options","fonts resize")]
    | "HausmanSL"        `elem` cls = playTemplate [("system", "hausmanSL"), ("guides","hausman"), ("options","fonts resize")]
    | "HowardSnyderPL"   `elem` cls = playTemplate [("system", "howardSnyderPL"), ("guides","howardSnyder"), ("options","fonts resize")]
    | "HowardSnyderSL"   `elem` cls = playTemplate [("system", "howardSnyderSL"), ("guides","howardSnyder"), ("options","fonts resize")]
    | "HurleyPL"         `elem` cls = playTemplate [("system", "hurleyPL"), ("guides", "hurley"), ("options", "resize")]
    | "HurleySL"         `elem` cls = playTemplate [("system", "hurleySL"), ("guides", "hurley"), ("options", "resize")]
    | "IchikawaJenkinsQL"`elem` cls = playTemplate [("system", "ichikawaJenkinsQL"), ("options","render")]
    | "IchikawaJenkinsSL"`elem` cls = playTemplate [("system", "ichikawaJenkinsSL"), ("options","render")]
    | "JohnsonSL"        `elem` cls = playTemplate [("system", "johnsonSL")]
    | "JohnsonSLPlus"    `elem` cls = playTemplate [("system", "johnsonSLPlus")]
    | "LogicBookPD"      `elem` cls = playTemplate [("system", "LogicBookPD")]
    | "LogicBookPDE"     `elem` cls = playTemplate [("system", "LogicBookPDE")]
    | "LogicBookPDEPlus" `elem` cls = playTemplate [("system", "LogicBookPDEPlus")]
    | "LogicBookPDPlus"  `elem` cls = playTemplate [("system", "LogicBookPDPlus")]
    | "LogicBookSD"      `elem` cls = playTemplate [("system", "LogicBookSD")]
    | "LogicBookSDPlus"  `elem` cls = playTemplate [("system", "LogicBookSDPlus")]
    | "MontagueQC"       `elem` cls = playTemplate [("system", "montagueQC"),("options","resize")]
    | "MontagueSC"       `elem` cls = playTemplate [("system", "montagueSC"),("options","resize")]
    | "PolySecondOrder"  `elem` cls = playTemplate [("system", "polyadicSecondOrder")]
    | "Prop"             `elem` cls = playTemplate [("system", "prop")]
    | "GregorySD"        `elem` cls = playTemplate [("system", "gregorySD"),("guides","fitch"),("options","indent fonts resize render")]
    | "GregorySDE"       `elem` cls = playTemplate [("system", "gregorySDE"),("guides","fitch"),("options","indent fonts resize render")]
    | "GregoryPD"        `elem` cls = playTemplate [("system", "gregoryPD"),("guides","fitch"),("options","indent fonts resize render")]
    | "GregoryPDE"       `elem` cls = playTemplate [("system", "gregoryPDE"),("guides","fitch"),("options","indent fonts resize render")]
    | "SecondOrder"      `elem` cls = playTemplate [("system", "secondOrder")]
    | "SeparativeST"     `elem` cls = playTemplate [("system", "separativeSetTheory"), ("options","resize render")]
    | "TomassiPL"        `elem` cls = playTemplate [("system", "tomassiPL"), ("options","resize render hideNumbering")]
    | "TomassiQL"        `elem` cls = playTemplate [("system", "tomassiQL"), ("options","resize render hideNumbering")]
    | "WinklerFOL"       `elem` cls = playTemplate [("system", "winklerFOL"), ("guides", "fitch"), ("options", "resize")]
    | "WinklerTFL"       `elem` cls = playTemplate [("system", "winklerTFL"), ("guides", "fitch"), ("options", "resize")]
    | "ZachFOL"          `elem` cls = playTemplate [("system", "thomasBolducAndZachFOL"), ("options","render")]
    | "ZachFOL2019"      `elem` cls = playTemplate [("system", "thomasBolducAndZachFOL2019"), ("options","render")]
    | "ZachFOLCore"      `elem` cls = playTemplate [("system", "thomasBolducAndZachFOLCore"), ("options","render")]
    | "ZachFOLEq"        `elem` cls = playTemplate [("system", "zachFOLEq")]
    | "ZachFOLPlus2019"  `elem` cls = playTemplate [("system", "thomasBolducAndZachFOLPlus2019"), ("options","render")]
    | "ZachPropEq"       `elem` cls = playTemplate [("system", "zachPropEq")]
    | "ZachTFL"          `elem` cls = playTemplate [("system", "thomasBolducAndZachTFL"), ("options","render")]
    | "ZachTFL2019"      `elem` cls = playTemplate [("system", "thomasBolducAndZachTFL2019"), ("options","render")]
    | "ZachTFLCore"      `elem` cls = playTemplate [("system", "thomasBolducAndZachTFLCore"), ("options","render")]
    | otherwise = playTemplate []
    where fixed = [("type","proofchecker")]
          playTemplate opts = template (unions [fromList extra, fromList opts, fromList fixed]) "Playground" (unlines' $ formatChunk content)

template :: Map Text Text -> Text -> Text -> Block
template opts header content = exerciseWrapper (toList opts) header $ RawBlock "html"
        --Need rawblock here to get the linebreaks right.
        $ T.concat ["<div", optString, ">", content, "</div>"]
    where optString = T.concat $ map (\(x,y) -> (T.concat [" data-carnap-", x, "=\"", y, "\""])) (toList opts)
