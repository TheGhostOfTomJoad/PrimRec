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
import Syntax
import Text.Parsec
import Text.Parsec.Combinator ()
import Text.Parsec.Text.Lazy (Parser)
import qualified Text.Parsec.Token as Tok

pInteger :: Parser Int
pInteger = fromIntegral <$> Tok.natural lexer

pVariable :: Parser ExpN
pVariable = VarN <$> identifier

pColon :: Parser ()
pColon = reservedOp ":"

pNumber :: Parser ExpN
pNumber = NatN . fromIntegral <$> pInteger

pArgAndType :: Parser (String, Ty)
pArgAndType = (,) <$> identifier <* pColon <*> pTypeAtom <|> ((,) <$> identifier <* pColon <*> parens pType)

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

pPrek :: Parser ExpN
pPrek = PRecN <$ reserved "P" <*> pAtom

pAtom :: Parser ExpN
pAtom =
  pSuc
    <|> pLambda
    <|> pNumber
    <|> parens pExp
    <|> pLetIn
    <|> pVariable
    <|> pPrek

pSemi :: Parser ()
pSemi = reservedOp ";"

pTypeAtom :: Parser Ty
pTypeAtom =
  TyNat
    <$ reserved "Nat"
    <|> parens pType

pType :: Parser Ty
pType = foldr1 (:->) <$> sepBy pTypeAtom (reservedOp "->")

pExp :: Parser ExpN
pExp = foldl1 AppN <$> many1 pAtom

runParseExp :: L.Text -> Either ParseError ExpN
runParseExp = parse (contents pExp) "sourceFile"

runParseVar :: L.Text -> Either ParseError ExpN
runParseVar = parse (contents pVariable) "sourceFile"

-------------------------------------------------

data TopLevelExp = TopLevelDec String ExpN | TopLevelExp ExpN | Compare String String

haskellCode :: Parser String
haskellCode = const <$> string "[e|" *> manyTill anyChar (try (string "|] "))

pCompare :: Parser TopLevelExp
pCompare =
  Compare
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
