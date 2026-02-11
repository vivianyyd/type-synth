{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE FlexibleContexts #-}

module Main (main) where

import GHC.Paths (libdir)
-- Use the ghc‑lib versions of GHC API modules:
import GHC
import DynFlags        (DynFlags) --, setSessionDynFlags, getSessionDynFlagsl) already in ghc
import Outputable      (showSDocUnsafe, ppr, text, (<+>))
import TcRnTypes       (tcg_binds)
import CoreSyn         (CoreBind(..), Bind(Rec), Bind(NonRec))
import Var             (varType)
import HsBinds (LHsBind, HsBindLR(FunBind), HsBindLR(..))
import HscTypes (ModGuts, mg_binds)
import SrcLoc (unLoc)
import Data.List (find)
import Bag             (bagToList)
import HsExtension     (GhcTc)
import System.Environment (getArgs)
import Control.Monad.IO.Class (liftIO)



main :: IO ()
main = do
  args <- getArgs
  case args of
    [fp] -> runGhc (Just libdir) (go fp)
    _    -> putStrLn "Usage: PrintTypeVsCore <HaskellSource.hs>"

go :: FilePath -> Ghc ()
go fp = do
  dflags <- getSessionDynFlags
  _ <- setSessionDynFlags dflags
  target <- guessTarget fp Nothing
  addTarget target
  _ <- load LoadAllTargets
  
  --
--   modGraph <- depanal [] False
--   case find ((== mkModuleName (takeBaseName fp)) . moduleName . ms_mod) modGraph of
--     Nothing -> liftIO $ putStrLn "Module not part of module graph."
--     Just modSum -> do
--       parsed <- parseModule modSum
--       typechecked <- typecheckModule parsed
-- 
--       liftIO $ putStrLn "\n=== Typechecked HsSyn types (implicit constraints) ==="
--       let binds = tcg_binds (fst (tm_internals_ typechecked))
--       mapM_ (liftIO . printHsBindType) (bagToList binds)
-- 
--       desugared <- desugarModule typechecked
--       liftIO $ putStrLn "\n=== Core types (explicit dictionaries) ==="
--       let coreBinds = mg_binds (coreModule desugared)
--       mapM_ (liftIO . printCoreBindType) coreBinds
--   where
--     takeBaseName = reverse . takeWhile (/='.') . reverse
  --

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
    let var = unLoc fid
    in putStrLn $ showSDocUnsafe $ ppr var <+> text "::" <+> ppr (varType var)
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
