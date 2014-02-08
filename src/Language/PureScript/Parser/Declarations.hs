-----------------------------------------------------------------------------
--
-- Module      :  Language.PureScript.Parser.Declarations
-- Copyright   :  (c) Phil Freeman 2013
-- License     :  MIT
--
-- Maintainer  :  Phil Freeman <paf31@cantab.net>
-- Stability   :  experimental
-- Portability :
--
-- |
-- Parsers for module definitions and declarations
--
-----------------------------------------------------------------------------

module Language.PureScript.Parser.Declarations (
    parseDeclaration,
    parseModule,
    parseModules
) where

import Data.Maybe (isJust, fromMaybe)
import Control.Monad (when)
import Control.Applicative
import qualified Text.Parsec as P

import Language.PureScript.Names
import Language.PureScript.Parser.State
import Language.PureScript.Parser.Common
import Language.PureScript.Declarations
import Language.PureScript.Parser.Values
import Language.PureScript.Parser.Types
import Language.PureScript.Parser.Kinds
import Language.PureScript.CodeGen.JS.AST
import Language.PureScript.Values

parseDataDeclaration :: P.Parsec String ParseState Declaration
parseDataDeclaration = do
  reserved "data"
  name <- indented *> properName
  tyArgs <- many (indented *> identifier)
  _ <- lexeme $ indented *> P.char '='
  ctors <- sepBy1 ((,) <$> properName <*> P.optionMaybe (indented *> parsePolyType)) pipe
  return $ DataDeclaration name tyArgs ctors

parseTypeDeclaration :: P.Parsec String ParseState Declaration
parseTypeDeclaration =
  TypeDeclaration <$> P.try (parseIdent <* lexeme (indented *> P.string "::"))
                  <*> parsePolyType

parseTypeSynonymDeclaration :: P.Parsec String ParseState Declaration
parseTypeSynonymDeclaration =
  TypeSynonymDeclaration <$> (P.try (reserved "type") *> indented *> properName)
                         <*> many (indented *> identifier)
                         <*> (lexeme (indented *> P.char '=') *> parsePolyType)

parseValueDeclaration :: P.Parsec String ParseState Declaration
parseValueDeclaration =
  ValueDeclaration <$> parseIdent
                   <*> P.many parseBinderNoParens
                   <*> P.optionMaybe parseGuard
                   <*> ((lexeme (indented *> P.char '=')) *> parseValue)

parseExternDeclaration :: P.Parsec String ParseState Declaration
parseExternDeclaration = P.try (reserved "foreign") *> indented *> (reserved "import") *> indented *>
   (ExternDataDeclaration <$> (P.try (reserved "data") *> indented *> properName)
                             <*> (lexeme (indented *> P.string "::") *> parseKind)
   <|> do ident <- parseIdent
          js <- P.optionMaybe (JSRaw <$> stringLiteral)
          ty <- (lexeme (indented *> P.string "::") *> parsePolyType)
          return $ ExternDeclaration (if isJust js then InlineJavascript else ForeignImport) ident js ty)

parseAssociativity :: P.Parsec String ParseState Associativity
parseAssociativity =
  (P.try (reserved "infixl") >> return Infixl) <|>
  (P.try (reserved "infixr") >> return Infixr)

parseFixity :: P.Parsec String ParseState Fixity
parseFixity = Fixity <$> parseAssociativity <*> (indented *> natural)

parseFixityDeclaration :: P.Parsec String ParseState Declaration
parseFixityDeclaration = do
  fixity <- parseFixity
  indented
  name <- operator
  return $ FixityDeclaration fixity name

parseImportDeclaration :: P.Parsec String ParseState Declaration
parseImportDeclaration = do
  reserved "import"
  indented
  moduleName <- ModuleName <$> properName
  idents <- P.optionMaybe $ parens $ commaSep1 (Left <$> parseIdent <|> Right <$> properName)
  return $ ImportDeclaration moduleName idents

parseTypeClassDeclaration :: P.Parsec String ParseState Declaration
parseTypeClassDeclaration = do
  reserved "class"
  implies <- P.optionMaybe $ do
    indented
    implies <- parens (commaSep1 ((,) <$> parseQualified properName <*> parseType))
    reservedOp "<="
    return implies
  className <- indented *> properName
  ident <- indented *> identifier
  indented *> reserved "where"
  members <- mark (P.many (same *> parseTypeDeclaration))
  return $ TypeClassDeclaration className ident (fromMaybe [] implies) members

parseTypeInstanceDeclaration :: P.Parsec String ParseState Declaration
parseTypeInstanceDeclaration = do
  reserved "instance"
  deps <- P.optionMaybe $ do
    deps <- parens (commaSep1 ((,) <$> parseQualified properName <*> parseType))
    indented
    reservedOp "=>"
    return deps
  className <- indented *> parseQualified properName
  ty <- indented *> parseType
  indented *> reserved "where"
  members <- mark (P.many (same *> parseValueDeclaration))
  return $ TypeInstanceDeclaration (fromMaybe [] deps) className ty members

-- |
-- Parse a single declaration
--
parseDeclaration :: P.Parsec String ParseState Declaration
parseDeclaration = P.choice
                   [ parseDataDeclaration
                   , parseTypeDeclaration
                   , parseTypeSynonymDeclaration
                   , parseValueDeclaration
                   , parseExternDeclaration
                   , parseFixityDeclaration
                   , parseImportDeclaration
                   , parseTypeClassDeclaration
                   , parseTypeInstanceDeclaration ] P.<?> "declaration"

-- |
-- Parse a module header and a collection of declarations
--
parseModule :: P.Parsec String ParseState Module
parseModule = do
  reserved "module"
  indented
  name <- properName
  _ <- lexeme $ P.string "where"
  decls <- mark (P.many (same *> parseDeclaration))
  return $ Module name decls

-- |
-- Parse a collection of modules
--
parseModules :: P.Parsec String ParseState [Module]
parseModules = whiteSpace *> mark (P.many (same *> parseModule)) <* P.eof
