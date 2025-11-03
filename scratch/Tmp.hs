import GHC
import DynFlags
import Outputable (Outputable, showPpr)
import qualified GHC.Paths as Paths

import Data.Functor

runGhc' :: Ghc a -> IO a
runGhc' ga = do
    runGhc (Just Paths.libdir) $ do
        dflags <- getDynFlags
        let dflags2 = dflags { ghcLink   = NoLink
                             , hscTarget = HscNothing
                             }
        setSessionDynFlags dflags2
        ga

typeExample :: Ghc TypecheckedModule
typeExample = do
    target <- guessTarget "prettyPrint2dList.hs" Nothing
    setTargets [target]
    load LoadAllTargets
    modGraph <- depanal [] False
    let modSummary = head (mgModSummaries modGraph)
    parsed <- parseModule modSummary
    typechecked <- typecheckModule parsed
    return typechecked

compileExample :: Ghc CoreModule
--compileExample = compileToCoreModule "prettyPrint2dList.hs"
compileExample = compileToCoreSimplified "prettyPrint2dList.hs"

showPpr' :: (Functor m, Outputable a, HasDynFlags m) => a -> m String
showPpr' a = (flip showPpr) a <$> getDynFlags

-- main = runGhc' (typeExample >>= showPpr') >>= putStrLn

main = runGhc' (typeExample >>= showPpr' . tm_typechecked_source) >>= putStrLn
