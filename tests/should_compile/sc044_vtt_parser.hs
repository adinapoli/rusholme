-- VTT parser - real-world Haskell program
-- This parses WebVTT subtitle files
-- Original source: https://github.com/adinapoli/rusholme/issues/250

{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE TypeApplications #-}

import Data.Attoparsec.Text hiding (take)
import Data.Attoparsec.Combinator
import qualified Data.Text as T
import Data.Char
import Text.Printf (printf)
import System.Environment (getArgs)
import Control.Applicative
import Control.Monad
import Data.Time
import Text.RawString.QQ
import qualified Data.HashMap.Strict as HM
import qualified Data.List as L

data Subtitle = Subtitle
  { captionIdx :: Int
  , startTime :: String
  , endTime :: String
  , text :: T.Text
  } deriving (Show)

parseVTT :: T.Text -> Either String [Subtitle]
parseVTT vtt = parseOnly vttParser vtt

vttParser :: Parser [Subtitle]
vttParser = do
  _ <- string "WEBVTT" >> endOfLine -- ignore header
  subtitles <- many subtitleParser
  pure subtitles

subtitleParser :: Parser Subtitle
subtitleParser = do
  skipWhile (not . isDigit)
  captionIndex <- decimal @Int <* endOfLine
  _ <- decimal @Int <* char ":" -- hours
  m <- decimal @Int <* char ":" -- minutes
  s <- double <* string " --> " -- seconds and arrow separator
  _ <- decimal @Int <* char ":" -- hours (again)
  m' <- decimal @Int <* char ":" -- minutes (again)
  s' <- double <* optional endOfLine -- seconds (again) and optional end of line
  let startTime = formatTime m s
      endTime = formatTime m' s'
      formatTime m s = printf "%02d:%06.3f" m s :: String
  text <- manyTill anyChar (try endOfLine <|> endOfInput)
  return $ Subtitle captionIndex startTime endTime (T.pack text)

-- Example usage:
main :: IO ()
main = do
  vttFile <- head <$> getArgs
  vtt <- readFile vttFile
  case parseVTT (T.pack vtt) of
    Left err -> putStrLn err
    Right subtitles -> print subtitles
  case parseOnly (many subtitleParser) mySub of
    Left err -> putStrLn err
    Right subtitles -> print subtitles

mySub :: T.Text
mySub = [r|

288
00:15:44.039 --> 00:15:49.210
it would make sense to try and get all of our denominators as seven. Right?

289
00:15:49.599 --> 00:15:51.900
What have I got to do to 14 to get it back to seven?

46
00:02:14.750 --> 00:02:17.399
You could have quite simply put zero|]
