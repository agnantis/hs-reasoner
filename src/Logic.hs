{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeOperators #-}

module Logic where

import Control.Eff
import Control.Eff.Reader.Lazy


data Expression
  = Simple String
  | Negative Expression
  | And Expression Expression
  | Or Expression Expression
  deriving (Show, Eq)

simplify :: Expression -> Expression
simplify (Negative (Negative e)) = simplify e
simplify (Negative (And e1 e2))  = Or (simplify (Negative e1)) (simplify (Negative e2))
simplify (Negative (Or e1 e2))   = And (simplify (Negative e1)) (simplify (Negative e2))
simplify s = s


------------------------------
-- [PoC] Extensible Effects --
------------------------------

-- The Poc will include a:
--  - State: with a list
--  - Exception Handling
--  - Logging
--  - Configuration


-- Data types


newtype AppState = AppSate [Int]
data Config = Config
  { logLevel :: LogLevel
  , outDir   :: FilePath
  }

data Connection = Connection
  { name :: String
  }

data LogLevel = Info | Warning | Error deriving (Show, Eq, Ord)

getLogLevel' :: (Reader Config <:: r) => String -> Eff r String
getLogLevel' prefix = do
  Config _ o <- ask
  Config _ _ <- ask
  pure $ prefix ++ o 

getLogLevel :: ([Reader Config, Reader Connection] <:: r) => String -> Eff r String
getLogLevel prefix = do
  Connection o3 <- ask
  Config _ o <- ask
  Config _ _ <- ask
  pure $ prefix ++ o ++ " (" ++ o3 ++ ")"

defaultConfig :: Config
defaultConfig = Config Info "/usr/log"

defaultConnection :: Connection
defaultConnection = Connection "TCP/IP"

runMe :: String
runMe = run . runReader defaultConnection . runReader defaultConfig $ getLogLevel "Path: "


