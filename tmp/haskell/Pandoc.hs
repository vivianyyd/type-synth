module Main where
import Text.Pandoc
import Data.Text (Text)
import qualified Data.Text.IO as T

mdToRST :: Text -> IO Text
mdToRST txt = runIOorExplode $
  readMarkdown def txt
  >>= writeRST def{ writerReferenceLinks = True }

main :: IO ()
main = do
  T.getContents >>= mdToRST >>= T.putStrLn
