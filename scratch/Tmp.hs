import GHC
import DynFlags
import Outputable (Outputable, showPpr, showSDocUnsafe, ppr, text, (<+>))
import qualified GHC.Paths as Paths
import Data.Functor

import Control.Monad.IO.Class (liftIO)
import Var             (varType)
import TcRnTypes       (tcg_binds)
import Bag             (bagToList)


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
    target <- guessTarget "Simple.hs" Nothing
    setTargets [target]
    load LoadAllTargets
    modGraph <- depanal [] False
    let modSummary = head (mgModSummaries modGraph)
    let modSummary = head [ m | m <- mgModSummaries modGraph
                              , ms_hspp_file m == "Simple.hs" ]
    parsed <- parseModule modSummary
    typechecked <- typecheckModule parsed
    return typechecked

compileExample :: Ghc CoreModule
--compileExample = compileToCoreModule "prettyPrint2dList.hs"
compileExample = compileToCoreSimplified "Simple.hs"

showPpr' :: (Functor m, Outputable a, HasDynFlags m) => a -> m String
showPpr' a = (flip showPpr) a <$> getDynFlags

printHsBindType :: LHsBind GhcTc -> IO ()
printHsBindType lb = case unLoc lb of
  FunBind {fun_id = fid} ->
    let var = unLoc fid
    in putStrLn $ showSDocUnsafe $ ppr var <+> text "::" <+> ppr (varType var)
  _ -> return ()


-- main = runGhc' (typeExample >>= showPpr') >>= putStrLn

-- main = runGhc' (typeExample >>= showPpr' . tm_typechecked_source) >>= putStrLn

main :: IO ()
main = runGhc (Just Paths.libdir) $ do
    dflags <- getSessionDynFlags
    _ <- setSessionDynFlags dflags
    -- todo copy code above instead     
    
    typechecked <- typeExample

    liftIO $ putStrLn "\n=== Typechecked HsSyn types ==="

    let binds = tm_typechecked_source typechecked
    --let (tcg, _) = tm_internals_ typechecked
      --  binds     = tcg_binds tcg

    mapM_ (liftIO . printHsBindType) (bagToList binds)
