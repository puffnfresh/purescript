-----------------------------------------------------------------------------
--
-- Module      :  Language.PureScript.Error
-- Copyright   :  (c) 2013-14 Phil Freeman, (c) 2014 Gary Burgess, and other contributors
-- License     :  MIT
--
-- Maintainer  :  Phil Freeman <paf31@cantab.net>
-- Stability   :  experimental
-- Portability :
--
-- |
--
-----------------------------------------------------------------------------

{-# LANGUAGE GeneralizedNewtypeDeriving, FlexibleContexts #-}

module Language.PureScript.Errors where

import Data.List (intercalate)
import Data.Monoid

import Control.Monad.Error

import Language.PureScript.Declarations
import Language.PureScript.Pretty
import Language.PureScript.Types

-- |
-- Type for sources of type checking errors
--
data ErrorSource
  -- |
  -- An error which originated at a Value
  --
  = ValueError Value
  -- |
  -- An error which originated at a Type
  --
  | TypeError Type deriving (Show)

-- |
-- Compilation errors
--
data CompileError = CompileError {
    -- |
    -- Error message
    --
    compileErrorMessage :: String
    -- |
    -- The value where the error occurred
    --
  , compileErrorValue :: Maybe ErrorSource
    -- |
    -- Optional source position information
    --
  , compileErrorPosition :: Maybe SourcePos
  } deriving (Show)

-- |
-- A stack trace for an error
--
newtype ErrorStack = ErrorStack { runErrorStack :: [CompileError] } deriving (Show, Monoid)

instance Error ErrorStack where
  strMsg s = ErrorStack [CompileError s Nothing Nothing]
  noMsg = ErrorStack []

prettyPrintErrorStack :: Bool -> ErrorStack -> String
prettyPrintErrorStack printFullStack (ErrorStack es) =
  case mconcat $ map (Last . compileErrorPosition) es of
    Last (Just sourcePos) -> "Error at " ++ show sourcePos ++ ": \n" ++ prettyPrintErrorStack'
    _ -> prettyPrintErrorStack'
  where
  prettyPrintErrorStack' :: String
  prettyPrintErrorStack'
    | printFullStack = intercalate "\n" (map showError (filter isErrorNonEmpty es))
    | otherwise =
      let
        es' = filter isErrorNonEmpty es
      in case length es' of
        1 -> showError (head es')
        _ -> showError (head es') ++ "\n" ++ showError (last es')

stringifyErrorStack :: Bool -> Either ErrorStack a -> Either String a
stringifyErrorStack printFullStack = either (Left . prettyPrintErrorStack printFullStack) Right

isErrorNonEmpty :: CompileError -> Bool
isErrorNonEmpty = not . null . compileErrorMessage

showError :: CompileError -> String
showError (CompileError msg Nothing _) = msg
showError (CompileError msg (Just (ValueError val)) _) = "Error in value " ++ prettyPrintValue val ++ ":\n" ++ msg
showError (CompileError msg (Just (TypeError ty)) _) = "Error in type " ++ prettyPrintType ty ++ ":\n" ++ msg

mkErrorStack :: String -> Maybe ErrorSource -> ErrorStack
mkErrorStack msg t = ErrorStack [CompileError msg t Nothing]

positionError :: SourcePos -> ErrorStack
positionError pos = ErrorStack [CompileError "" Nothing (Just pos)]

-- |
-- Rethrow an error with a more detailed error message in the case of failure
--
rethrow :: (MonadError e m) => (e -> e) -> m a -> m a
rethrow f = flip catchError $ \e -> throwError (f e)

-- |
-- Rethrow an error with source position information
--
rethrowWithPosition :: (MonadError ErrorStack m) => SourcePos -> m a -> m a
rethrowWithPosition pos = rethrow (positionError pos <>)
