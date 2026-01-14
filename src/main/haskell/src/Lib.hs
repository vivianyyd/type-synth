{-
module MyLib (someFunc) where

someFunc :: IO ()
someFunc = putStrLn "someFunc"
AST
module Lib
  ( renderMarkdown
  ) where

-}
module Lib where

import ModuleA (greet)

import Text.Pandoc
import qualified Data.Text as T

{-
renderMarkdown :: String -> IO String
renderMarkdown input = do
  let pandocResult = runPure $ readMarkdown def (T.pack input) >>= writeHtml5String def
  pandocResult
  case pandocResult of
    Left err -> return $ "Error: " ++ show err
    Right html -> return $ T.unpack html
-}
