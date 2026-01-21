module Main where

import System.Environment (getArgs)
import System.Exit (exitFailure)
import System.IO (hPutStrLn, stderr)
import Typecheck (typecheckLines)

main :: IO ()
main = do
  args <- getArgs
  contents <- case args of
    [] -> getContents
    [path] -> readFile path
    _ -> do
      hPutStrLn stderr "Usage: hs-typecheck [FILE]"
      exitFailure
  result <- typecheckLines (lines contents)
  case result of
    Left err -> hPutStrLn stderr (show err)
    Right outputs -> mapM_ putStrLn outputs
