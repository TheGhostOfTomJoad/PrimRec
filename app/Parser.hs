module Parser
  ( runParseExp,
    runParseTopLevelExp,
    TopLevelExp (..),
    pModule,
    pModule2,
    runParseVar,
  )
where

-- source: https://github.com/sdiehl/write-you-a-haskell/tree/ae73485e045ef38f50846b62bd91777a9943d1f7/chapter7/poly_constraints/src

import qualified Data.Text.Lazy as L
import Lexer
import Lib.Nat as Nat
  ( Nat,
    fromInt,
  )
import Syntax
import Text.Parsec
import Text.Parsec.Combinator ()
import Text.Parsec.Text.Lazy (Parser)
import qualified Text.Parsec.Token as Tok

pInteger :: Parser Int
pInteger = fromIntegral <$> Tok.natural lexer

pNat :: Parser Nat
pNat = Nat.fromInt <$> Tok.natural lexer

pVariable :: Parser ExpN
pVariable = VarN <$> identifier

pColon :: Parser ()
pColon = reservedOp ":"

pNumber :: Parser ExpN
pNumber = NatN . fromIntegral <$> pInteger

pArgAndType :: Parser (String, Ty)
pArgAndType = (,) <$> identifier <* pColon <*> pTypeAtom <|>  ((,) <$> identifier <* pColon <*> parens pType )

pArgsAndTypes :: Parser [(String, Ty)]
pArgsAndTypes = many1 pArgAndType

pLambda :: Parser ExpN
pLambda =
  flip (foldr (uncurry LamN))
    <$ reservedOp "\\"
    <*> pArgsAndTypes
    <* reservedOp "->"
    <*> pExp

pLetIn :: Parser ExpN
pLetIn =
  LetN
    <$ reserved "let"
    <*> identifier
    <* reservedOp "="
    <*> pExp
    <* reserved "in"
    <*> pExp

pSuc :: Parser ExpN
pSuc = SuccN <$ reserved "S"

pConstZero :: Parser ExpN
pConstZero = ConstZeroN <$ reserved "Z" <*> (fromIntegral <$> pInteger)

pProjN :: Parser ExpN
pProjN =
  ProjN
    <$ reserved "Pi"
    <*> (fromIntegral <$> pInteger)
    <*> (fromIntegral <$> pInteger)

pComp :: Parser ExpN
pComp = CompN <$ reserved "C" <*> pAtom <*> pAtom

pPrek :: Parser ExpN
pPrek = PRecN <$ reserved "P" <*> pAtom <*> pAtom

pRun :: Parser ExpN
pRun = RunPrekN <$ reserved "run" <*> pAtom

pAtom :: Parser ExpN
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

pListExp :: Parser [ExpN]
pListExp = sqrBrackets (sepBy pAtom pComma)

toListExp :: Maybe Ty -> [ExpN] -> ExpN
toListExp ty = foldr ConsN (NilN ty)

pList :: Parser ExpN
pList = toListExp <$> pMaybeType <*> pListExp

pExp :: Parser ExpN
pExp = foldl1 AppN <$> many1 pAtom

runParseExp :: L.Text -> Either ParseError ExpN
runParseExp = parse (contents pExp) "sourceFile"

runParseVar :: L.Text -> Either ParseError ExpN
runParseVar = parse (contents pVariable) "sourceFile"

-------------------------------------------------

data TopLevelExp = TopLevelDec String ExpN | TopLevelExp ExpN | Compare' String String

haskellCode :: Parser String
haskellCode = const <$> string "[e|" *> manyTill anyChar (try (string "|] "))

pCompare :: Parser TopLevelExp
pCompare =
  Compare'
    <$ reserved "compare"
    <*> haskellCode
    <* reservedOp "with"
    <*> identifier

pTopLevelLet :: Parser TopLevelExp
pTopLevelLet =
  uncurry TopLevelDec
    <$> pTopLevelLetHelper

pTopLevelLetHelper :: Parser (String, ExpN)
pTopLevelLetHelper =
  (,)
    <$ reserved "let"
    <*> identifier
    <* reservedOp "="
    <*> pExp

pTopLEvelExp :: Parser TopLevelExp
pTopLEvelExp = pCompare <|> pTopLevelLet <|> TopLevelExp <$> pExp

runParseTopLevelExp :: L.Text -> Either ParseError TopLevelExp
runParseTopLevelExp = parse (contents pTopLEvelExp) "cmd"

pModule :: L.Text -> Either ParseError [(String, ExpN)]
pModule = parse (contents (sepEndBy pTopLevelLetHelper pSemi)) "pModule"

pModule2 :: L.Text -> Either ParseError [TopLevelExp]
pModule2 = parse (contents (sepEndBy pTopLEvelExp pSemi)) "pModule2"
