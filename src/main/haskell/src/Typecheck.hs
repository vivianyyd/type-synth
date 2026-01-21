{-# LANGUAGE ScopedTypeVariables #-}

module Typecheck (typecheckLines) where

import Control.Monad (void)
import Data.Char (isSpace)
import Data.List (dropWhileEnd, isInfixOf, isPrefixOf, nub)
import Data.Maybe (mapMaybe)
import GHC
import GHC.Driver.Session (ghcLink, hscTarget)
import GHC.Paths (libdir)

data ParsedLine
  = ImportLine String
  | DefinitionLine String
  | ExprLine String

typecheckLines :: [String] -> IO (Either SourceError [String])
typecheckLines inputLines = runGhc (Just libdir) $ do
  let parsedLines = mapMaybe parseLine inputLines
      imports = nub ("Prelude" : [spec | ImportLine spec <- parsedLines])
      definitions = [def | DefinitionLine def <- parsedLines]
      expressions = [expr | ExprLine expr <- parsedLines]
  dflags <- getSessionDynFlags
  void $ setSessionDynFlags dflags { hscTarget = HscInterpreted, ghcLink = LinkInMemory }
  setContext (map (IIDecl . simpleImportDecl . mkModuleName) imports)
  mapM (checkOne definitions) expressions

checkOne :: [String] -> String -> Ghc String
checkOne definitions expr =
  handleSourceError (\_ -> pure ("ERR\t" ++ expr)) $ do
    void (exprType (wrapDefinitions definitions expr))
    pure ("OK\t" ++ expr)

wrapDefinitions :: [String] -> String -> String
wrapDefinitions [] expr = expr
wrapDefinitions definitions expr =
  unlines ("let" : map ("  " ++) definitions ++ ["in " ++ expr])

parseLine :: String -> Maybe ParsedLine
parseLine line
  | null trimmed = Nothing
  | "--" `isPrefixOf` trimmed = Nothing
  | "{-#" `isPrefixOf` trimmed = Nothing
  | "{-" `isPrefixOf` trimmed = Nothing
  | "-}" `isPrefixOf` trimmed = Nothing
  | "module " `isPrefixOf` trimmed = Nothing
  | "import " `isPrefixOf` trimmed = parseImport trimmed
  | "_" `isPrefixOf` trimmed = Just (ExprLine (stripExpr trimmed))
  | "::" `isInfixOf` trimmed = Just (DefinitionLine trimmed)
  | '=' `elem` trimmed = Just (DefinitionLine trimmed)
  | otherwise = Just (ExprLine trimmed)
  where
    trimmed = trim line

parseImport :: String -> Maybe ParsedLine
parseImport line =
  case words line of
    ("import" : _ : moduleName : _) | "qualified" `elem` words line ->
      Just (ImportLine moduleName)
    ("import" : moduleName : _) ->
      Just (ImportLine moduleName)
    _ -> Nothing

stripExpr :: String -> String
stripExpr line =
  case dropWhile isSpace line of
    '_' : rest ->
      case dropWhile isSpace rest of
        '=' : rhs -> trim rhs
        _ -> trim line
    _ -> trim line

trim :: String -> String
trim = dropWhileEnd isSpace . dropWhile isSpace
