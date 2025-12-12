{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE FlexibleContexts #-}

module Main where

import GHC hiding (parseModule, typecheckModule, desugarModule)
import GHC.Paths (libdir)
import GHC.Driver.Session (DynFlags)
import GHC.Utils.Outputable (showSDocUnsafe, ppr, text, (<+>))
import GHC.Tc.Types (tcg_binds)
import GHC.Core (varType, CoreBind(..))
import Control.Monad.IO.Class (liftIO)
import System.Environment (getArgs)
import Data.Maybe (fromMaybe)
import GHC.Data.Bag (bagToList)
import GHC.Hs.Binds (LHsBind, FunBind(..), unLoc)
import GHC.Hs.Extension (GhcTc)

main :: IO ()
main = do
  args <- getArgs
  case args of
    [fp] -> runGhc (Just libdir) (go fp)
    _    -> putStrLn "Usage: PrintTypeVsCore <HaskellSource.hs>"

go :: FilePath -> Ghc ()
go fp = do
  dflags <- getSessionDynFlags >>= setSessionDynFlags
  target <- guessTarget fp Nothing
  addTarget target
  _ <- load LoadAllTargets

  modSum <- getModSummary =<< guessModuleName fp
  parsed <- parseModule modSum
  typechecked <- typecheckModule parsed

  liftIO $ putStrLn "\n=== Typechecked HsSyn types (implicit constraints) ==="
  let binds = tcg_binds (fst (tm_internals_ typechecked))
  mapM_ (liftIO . printHsBindType) (bagToList binds)

  desugared <- desugarModule typechecked
  liftIO $ putStrLn "\n=== Core types (explicit dictionaries) ==="
  let coreBinds = mg_binds (coreModule desugared)
  mapM_ (liftIO . printCoreBindType) coreBinds

-- Helpers
printHsBindType :: LHsBind GhcTc -> IO ()
printHsBindType lb = case unLoc lb of
  FunBind {fun_id = fid} ->
    putStrLn $ showSDocUnsafe $ ppr fid <+> text "::" <+> ppr (varType fid)
  _ -> return ()

printCoreBindType :: CoreBind -> IO ()
printCoreBindType = \case
  NonRec b _ -> putStrLn $ showSDocUnsafe $ ppr b <+> text "::" <+> ppr (varType b)
  Rec bs     -> mapM_ (\(b,_) -> putStrLn $ showSDocUnsafe $ ppr b <+> text "::" <+> ppr (varType b)) bs

-- Guess module name from filename
guessModuleName :: FilePath -> Ghc ModuleName
guessModuleName fp = return $ mkModuleName (takeBaseName fp)
  where
    takeBaseName = reverse . takeWhile (/='.') . reverse


