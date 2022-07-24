module Parser where

-- source: https://github.com/sdiehl/write-you-a-haskell/tree/ae73485e045ef38f50846b62bd91777a9943d1f7/chapter7/poly_constraints/src

import qualified Data.Text.Lazy as L
import Lexer
-- import Syntax

import Lib.Nat
import qualified Lib.Nat as Nat
import Syntax
import Text.Parsec
import Text.Parsec.Text.Lazy (Parser)
import qualified Text.Parsec.Token as Tok

pInteger :: Parser Int
pInteger = fromIntegral <$> Tok.natural lexer

pNat :: Parser Nat
pNat = Nat.fromInt <$> Tok.natural lexer

pVariable :: ExpN repr => Parser repr
pVariable = varN <$> identifier -- do
--   x <- identifier
--   return (VarN x)

pColon :: Parser ()
pColon = reservedOp ":"

pNumber :: ExpN repr => Parser repr
pNumber = natN . fromIntegral <$> pInteger

pArgAndType :: Parser (String, Ty)
pArgAndType = (,) <$> identifier <* pColon <*> pTypeAtom <|> ((,) <$> identifier <* pColon <*> parens pType)

pArgsAndTypes :: Parser [(String, Ty)]
pArgsAndTypes = many1 pArgAndType

pLambda :: ExpN repr => Parser repr
pLambda =
  flip (foldr (uncurry lamN))
    <$ reservedOp "\\"
    <*> pArgsAndTypes
    <* reservedOp "->"
    <*> pExp

pLetIn :: ExpN repr => Parser repr
pLetIn =
  letN
    <$ reserved "let"
    <*> identifier
    <* reservedOp "="
    <*> pExp
    <* reserved "in"
    <*> pExp

pSuc :: ExpN repr => Parser repr
pSuc = succN <$ reserved "S"

pConstZero :: ExpN repr => Parser repr
pConstZero = constZeroN <$ reserved "Z" <*> (fromIntegral <$> pInteger)

pProjN :: ExpN repr => Parser repr
pProjN =
  projN
    <$ reserved "Pi"
    <*> (fromIntegral <$> pInteger)
    <*> (fromIntegral <$> pInteger)

pComp :: ExpN repr => Parser repr
pComp = compN <$ reserved "C" <*> pAtom <*> pAtom

pPrek :: ExpN repr => Parser repr
pPrek = pRecN <$ reserved "P" <*> pAtom <*> pAtom

pRun :: ExpN repr => Parser repr
pRun = runPrekN <$ reserved "run" <*> pAtom

pAtom :: ExpN repr => Parser repr
pAtom =
  pSuc
    <|> pConstZero
    <|> pProjN
    <|> pComp
    <|> pPrek
    <|> pLambda
    <|> pNumber
    <|> pRun
    <|> parens pExp
    <|> pList
    <|> pLetIn
    <|> pVariable

pComma :: Parser ()
pComma = reservedOp ","

pSemi :: Parser ()
pSemi = reservedOp ";"

plBrSqr :: Parser ()
plBrSqr = reservedOp "["

prBrSqr :: Parser ()
prBrSqr = reservedOp "]"

pSmaller :: Parser ()
pSmaller = reservedOp "<"

pBigger :: Parser ()
pBigger = reservedOp ">"

pTypeAtom :: Parser Ty
pTypeAtom =
  TyNat
    <$ reserved "Nat"
    <|> TyList
      <$ reserved "Vec"
      <*> pNat
      <*> ( TyNat
              <$ reserved "Nat" <|> parens pType
          )
    <|> TyPrec
      <$ reserved "PR"
      <*> pNat
    <|> parens pType

pType :: Parser Ty
pType = foldr1 (:->) <$> sepBy pTypeAtom (reservedOp "->")

sqrBrackets :: Parser a -> Parser a
sqrBrackets = between plBrSqr prBrSqr

typeBraces :: Parser a -> Parser a
typeBraces = between pSmaller pBigger

{-# ANN pMaybeType "HLint: ignore" #-}
pMaybeType :: Parser (Maybe Ty)
pMaybeType = Just <$> typeBraces pType <|> pure Nothing

pListExp :: ExpN repr => Parser [repr]
pListExp = sqrBrackets (sepBy pAtom pComma)

splitLast :: [a] -> Maybe ([a], a)
splitLast [] = Nothing
-- splitLast [x] =Just ([],x)
splitLast (x : xs) = case splitLast xs of
  Nothing -> Just ([], x)
  Just (xs', x') -> Just (x : xs', x')

splitLast' :: [b] -> Maybe ([b], b)
splitLast' xs = case splitAt (length xs - 1) xs of
  (as, a : _) -> Just (as, a)
  _ -> Nothing

pListHelper :: ExpN repr => Maybe Ty -> [repr] -> repr
pListHelper maybeTy expList = case splitLast expList of
  Just (expList', exp) -> foldr consN (singN maybeTy exp) expList'
  Nothing -> nilN maybeTy

pList :: ExpN repr => Parser repr
pList = pListHelper <$> pMaybeType <*> pListExp

pExp :: ExpN repr => Parser repr
pExp = foldl1 appN <$> many1 pAtom

runParseExp :: ExpN repr => L.Text -> Either ParseError repr
runParseExp = parse (contents pExp) "sourceFile"

-------------------------------------------------

data TopLevelExp repr = TopLevelDec String repr | TopLevelExp repr | Compare' String String

haskellCode :: Parser String
haskellCode = const <$> string "[e|" *> manyTill anyChar (try (string "|] "))

pCompare :: Parser (TopLevelExp repr)
pCompare =
  Compare'
    <$ reserved "compare"
    <*> haskellCode
    <* reservedOp "with"
    <*> identifier

pTopLevelLet :: ExpN repr => Parser (TopLevelExp repr)
pTopLevelLet =
  uncurry TopLevelDec
    <$> pTopLevelLetHelper

pTopLevelLetHelper :: ExpN repr => Parser (String, repr)
pTopLevelLetHelper =
  (,)
    <$ reserved "let"
    <*> identifier
    <* reservedOp "="
    <*> pExp

pTopLEvelExp :: ExpN repr => Parser (TopLevelExp repr)
pTopLEvelExp = pCompare <|> pTopLevelLet <|> TopLevelExp <$> pExp

runParseTopLevelExp :: ExpN repr => L.Text -> Either ParseError (TopLevelExp repr)
runParseTopLevelExp = parse (contents pTopLEvelExp) "cmd"

pModule :: ExpN repr => L.Text -> Either ParseError [(String, repr)]
pModule = parse (contents (sepEndBy pTopLevelLetHelper pSemi)) "pModule"

pModule2 :: ExpN repr => L.Text -> Either ParseError [TopLevelExp repr]
pModule2 = parse (contents (sepEndBy pTopLEvelExp pSemi)) "pModule2"

runParseVar :: ExpN repr => L.Text -> Either ParseError repr
runParseVar = parse (contents pVariable) "sourceFile"
