module Lexer (lexer, identifier, reservedOp, reserved, parens, contents) where

-- source: https://github.com/sdiehl/write-you-a-haskell/tree/ae73485e045ef38f50846b62bd91777a9943d1f7/chapter7/poly_constraints/src

import Data.Functor.Identity
import qualified Data.Text.Lazy as L
import Text.Parsec
import Text.Parsec.Combinator ()
import qualified Text.Parsec.Expr ()
import Text.Parsec.Text.Lazy
import qualified Text.Parsec.Token as Tok

reservedNames :: [String]
reservedNames = ["S", "P", "let", "in", "Nat", "compare", "with"]

reservedOps :: [String]
reservedOps = ["->", "\\", ",", "=", ":", ";", "[e|", "|]"]

lexer :: Tok.GenTokenParser L.Text () Identity
lexer =
  Tok.makeTokenParser $
    Tok.LanguageDef
      { Tok.commentStart = "{-",
        Tok.commentEnd = "-}",
        Tok.commentLine = "--",
        Tok.nestedComments = True,
        Tok.identStart = lower,
        Tok.identLetter = alphaNum <|> oneOf "_'",
        Tok.opStart = oneOf "{}-\\>:=", 
        Tok.opLetter = oneOf "{}-\\>:=",
        Tok.reservedNames = reservedNames,
        Tok.reservedOpNames = reservedOps,
        Tok.caseSensitive = True
      }

reserved :: String -> Parser ()
reserved = Tok.reserved lexer

reservedOp :: String -> Parser ()
reservedOp = Tok.reservedOp lexer

identifier :: Parser String
identifier = Tok.identifier lexer

parens :: Parser a -> Parser a
parens = Tok.parens lexer

contents :: Parser a -> Parser a
contents p = Tok.whiteSpace lexer *> p <* eof
