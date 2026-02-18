-- GHC testsuite: record construction, update, and field access
module Sc030RecordUpdate where

data Config = Config
    { verbose  :: Bool
    , maxRetry :: Int
    , logFile  :: Maybe String
    } deriving (Show)

defaultConfig :: Config
defaultConfig = Config
    { verbose  = False
    , maxRetry = 3
    , logFile  = Nothing
    }

-- Record update
verboseConfig :: Config
verboseConfig = defaultConfig { verbose = True }

withLog :: String -> Config -> Config
withLog path cfg = cfg { logFile = Just path }

-- Nested record update
data App = App { config :: Config, name :: String }

setVerbose :: App -> App
setVerbose app = app { config = (config app) { verbose = True } }

-- Field access as function
getMaxRetry :: Config -> Int
getMaxRetry = maxRetry

-- Pattern matching on record
isVerbose :: Config -> Bool
isVerbose Config { verbose = v } = v
