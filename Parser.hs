{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE TupleSections #-}
module Parser where

import Control.Monad (void, when)
import Data.Functor.Identity (runIdentity)
import Control.Applicative hiding (Const, (<|>), many)
import Data.Monoid (Monoid(..))
import Data.List (foldl1')
import Control.Monad.State (State, get, put, evalStateT)
import Debug.Trace (trace)

import Text.Parsec hiding (State)
import Text.Parsec.Pos (initialPos)
import Text.Parsec.String
import qualified Text.Parsec.Token as Tok
import Text.Parsec.Language (haskellStyle, emptyDef)

import Expr (Const(..), Binder(..), Expr(..), Name(..),
             ConstTy(..), NameType(..), typeWith)
import Decl

{-
data PExpr n =
    PCore (Expr n)
  | PPar n
  | PTyped (PExpr n) (PExpr n)
  | PApp (PExpr n) (PExpr n)
  | PBind n (Binder (PExpr n)) (PExpr n)
  | PConst !Const
  | PTypeE !Int
  | PTypeI
  | PHole
  deriving (Show, Eq, Functor)
-}

{- TODO XXX: Implicit Args / Holes
-- id : {A : Type} -> A -> A
-- id = \a => a
--
-- test : Int
-- test = id _ 12
--
-- test = App (App 'id' Hole) 12
--
-- - App f _ : Int
--       |
-- -     f : 

-- term -> type -> term
fillHoles :: [(Name, Expr Name)] ->
             Expr Name -> Expr Name ->
             Either String (Expr Name)
fillHoles ctx (App f (Par Ref UName)) fxTy =
    let fTy = typeWith ctx f
    in case fTy of
        Left _  -> fTy
        Right (Bind n (Pi holeTy) body) ->
            

-- term -> type -> type
unify :: PExpr Name -> PExpr Name -> PExpr Name
unify (PBind n (Lam ty) )
unify (PPar n) (PPar m)
-}
{-
    let fTy = typeWith ctx f
    in undefined
-}
{-
fillHoles ctx (App f x) fxTy =
    PApp
        (fillHoles f (PBind UName (Pi ty) fxTy))
        (fillHoles x ty)
-}

{-
fillHoles :: PExpr Name -> PExpr Name -> Either String (PExpr Name)
fillHoles (PCore _) _ = Left "fillHoles: PCore 1"
fillHoles _ (PCore _) = Left "fillHoles: PCore 2"
fillHoles p@PPar{} ty = Right $ PTyped p ty
fillHoles (PTyped expr ty) = 
-}
{-
parsedToCore :: PExpr Name -> Expr Name
parsedToCore (PCore c) = c
parsedToCore (PPar n) =
    Par Ref n -- TODO: Test if it is a Data constructor.
parsedToCore (PApp f x) = App (parsedToCore f) (parsedToCore x)
parsedToCore (PBind n b x) =
    Bind n (fmap parsedToCore b) (parsedToCore x)
parsedToCore (PConst c) = Const c
parsedToCore (PTypeE i) = Type i
parsedToCore PTypeI = Type 0 -- TODO
parsedToCore PHole = trace "parsedToCore Recieved Hole!" $
    Par Ref (SName "_")
-}

type IParser a = ParsecT String () (State SourcePos) a

tokenParser :: Tok.GenTokenParser String a (State SourcePos)
tokenParser = Tok.makeTokenParser
    emptyDef {
        Tok.reservedOpNames = [":", "=", "\\", "|", "->", "=>"],
        Tok.reservedNames = ["data", "where", "Type"],

        Tok.commentStart = "{-",
        Tok.commentEnd = "-}",
        Tok.commentLine = "--",
        Tok.nestedComments = True,
        Tok.identStart = letter,
        Tok.identLetter = alphaNum <|> oneOf "_'",
        Tok.opStart = oneOf ":!#$%&*+./<=>?@\\^|-~",
        Tok.opLetter = oneOf ":!#$%&*+./<=>?@\\^|-~",
        Tok.caseSensitive = True
    }

reservedOp :: String -> IParser ()
reservedOp = Tok.reservedOp tokenParser

reserved :: String -> IParser ()
reserved = Tok.reserved tokenParser

ident :: IParser Name
ident = SName <$> Tok.identifier tokenParser
    <?> "ident"

lexeme :: IParser a -> IParser a
lexeme = Tok.lexeme tokenParser

parens :: IParser a -> IParser a
parens = Tok.parens tokenParser

-----------------
-- Data Parser --
-----------------

iparse :: IParser a -> SourceName -> String -> Either ParseError a
iparse p n s = runIdentity $
    flip evalStateT (initialPos n) $ runParserT p () n s

testDecl = iparse decl "testDecl" $ --"test = Maybe a -> a"
    "test : Type 0\ntest = Int"
{-
    "data Maybe : Type 0 -> Type 0 where\n" ++
    "    Just : (a : Type 0) -> a -> Maybe a\n" ++
    "    Nothing : (a : Type 0) -> Maybe a\n"
-}

decl :: IParser (PDecl (Expr Name))
decl = try caf <|> (Data <$> dataDecl)

caf :: IParser (PDecl (Expr Name))
caf = do
    (nameT, ty)   <- cafType
--    (nameB, expr) <- indented cafBody
    checkIndent
    (nameB, expr) <- cafBody
    if nameT /= nameB
        then error "Parser.caf: names don't match."
        else return $ Caf nameT expr ty

cafType :: IParser (Name, Expr Name)
cafType = (,) <$> (lexeme ident <* lexeme (reservedOp ":"))
              <*> lexeme parseExpr

cafBody :: IParser (Name, Expr Name)
cafBody = (,) <$> (lexeme ident <* lexeme (reservedOp "="))
              <*> lexeme parseExpr

dataDecl :: IParser (PData (Expr Name))
dataDecl = uncurry PDataDecl <$> lexeme dataDeclTy <*> block dataDeclCon

dataDeclTy :: IParser (Name, Expr Name)
dataDeclTy =
    between (lexeme (reserved "data"))
            (lexeme (reserved "where"))
            (lexeme (typedIdent))

dataDeclCon :: IParser (Name, Expr Name)
dataDeclCon = lexeme typedIdent
{- liftA2 (:) (lexeme typedIdent) . many $
    lexeme (reservedOp "|") *>
    lexeme typedIdent -}

------------
-- Parser --
------------

parseExpr :: IParser (Expr Name)
parseExpr = try piLam <|> try lambda <|> try app <|> atom
    <?> "expr"

app :: IParser (Expr Name)
app = do
    foldl1' App <$> many1 (sameOrIndented $ lexeme atom) <?> "app"

atom :: IParser (Expr Name)
atom = try constant <|> try var <|> parens parseExpr <?> "atom"

lambda :: IParser (Expr Name)
lambda = (do
    reservedOp "\\"
    (name, ty) <- same . lexeme $ parens typedIdent
    same . lexeme $ reservedOp "=>"
    body <- sameOrIndented parseExpr
    return $ Bind name (Lam ty) body
    ) <?> "lambda"

piLam :: IParser (Expr Name)
piLam = (do
    (name, pit) <-
            try ((\(n,t) -> (n, Pi t)) <$> lexeme (parens typedIdent))
        <|>     (UName,) . Pi <$> (try lambda <|> try app <|> atom)
    sameOrIndented . lexeme $ reservedOp "->"
    body <- sameOrIndented $ lexeme parseExpr
    return $ Bind name pit body
    ) <?> "piLam"

var :: IParser (Expr Name)
var = Par Ref <$> ident

constant :: IParser (Expr Name)
constant = Const <$> (try constVal <|> try (ConstTy <$> constTy))
                 <|> typeUniverse
    <?> "constant"

constVal :: IParser Const
constVal =
     try (ConstStr               <$> Tok.stringLiteral tokenParser)
 <|> try (ConstFlt . realToFrac  <$> Tok.float tokenParser)
 <|>     (ConstInt . fromInteger <$> Tok.integer tokenParser)
 <?> "constVal"

constTy :: IParser ConstTy
constTy =
        try (IntTy <$ string "Int")
    <|> try (FltTy <$ string "Float")
    <|>     (StrTy <$ string "String")
    <?> "constTy"

typeUniverse :: IParser (Expr Name)
typeUniverse = lexeme (reserved "Type") *>
    (Type . read <$> option "0" (sameOrIndented $ many1 digit))

typedIdent :: IParser (Name, Expr Name)
typedIdent =
    (,) <$> lexeme ident <*  sameOrIndented (lexeme (char ':'))
                         <*> sameOrIndented (lexeme  parseExpr)
    <?> "typedIdent"

test = iparse (allOf parseExpr) "test" "\\(whatever : Int) => 123.32 whatever"

idd = iparse (allOf parseExpr) "idd"
    "\\(A : Type 0 -> Type 0) => A"

ide = iparse (allOf parseExpr) "ide"
        "(\\(A : Type 0) => \\(f : A -> A) => \\(x : A) => f x) Int plus"

sameOrIndented :: IParser a -> IParser a
sameOrIndented p = sameOrIndentCheck >> p

sameOrIndentCheck :: IParser ()
sameOrIndentCheck = checkSame <|> indent

indented :: IParser a -> IParser a
indented x = indent >> x

indent :: IParser ()
indent = do
    pos <- getPosition
    s <- get
    if sourceColumn pos <= sourceColumn s
        then parserFail "not indented"
    else put $ setSourceLine s (sourceLine pos)

same :: IParser a -> IParser a
same x = checkSame >> x

checkSame :: IParser ()
checkSame = do
    pos <- getPosition
    s <- get
    when (sourceLine pos /= sourceLine s) $
        parserFail "over one line"

block :: IParser a -> IParser [a]
block p = withPos $ do
    r <- many1 (checkIndent >> p)
    return r

withPos :: IParser a -> IParser a
withPos x = do
    a <- get
    p <- getPosition
    r <- put p >> x
    put a >> return r

checkIndent :: IParser ()
checkIndent = do
    s <- get
    p <- getPosition
    when (sourceColumn p /= sourceColumn s) $
        parserFail "indentation doesn't match"

allOf :: IParser a -> IParser a
allOf p = Tok.whiteSpace tokenParser *> p <* eof

infixr 5 <++>
(<++>) :: Monoid a => IParser a -> IParser a -> IParser a
(<++>) = liftA2 mappend

testExpr :: Expr String
testExpr = App (Bind "val" (Lam (Const $ ConstTy IntTy)) (Var 0))
           (Const (ConstInt 12))

{-
data PExpr n =
    PVar n
  | PApp (PExpr n) (PExpr n)
  | PBind n (Binder (PExpr n)) (PExpr n)
  | PConst !Const
  | PIType
  | PEType !Int
  deriving (Show, Eq, Functor)

--parsedToCore :: PExpr n -> Expr n
--parsedToCore (PVar n)

tokenParser :: Tok.TokenParser a
tokenParser = Tok.makeTokenParser haskellStyle

topParse :: IParser (PExpr Name)
topParse =
    try lambda <|> try piLam <|> try app <|> atom
    <?> "topParse"

app :: IParser (PExpr Name)
app = foldr1 PApp <$> many1 (atom <* spaces) <?> "app"

atom :: IParser (PExpr Name)
atom = try constant <|> try var <|> paren topParse <?> "atom"

lambda :: IParser (PExpr Name)
lambda = (do
    void $ Tok.reservedOp tokenParser "\\"
    (name, ty) <- paren typedIdent
    spaces
    void $ Tok.reservedOp tokenParser "=>"
    spaces
    body <- topParse
    return $ PBind name (Lam ty) body
    ) <?> "lambda"

piLam :: IParser (PExpr Name)
piLam = (do
    (name, pit) <- try ((\(n,t) -> (n, Pi t)) <$> paren typedIdent)
               <|> try ((\n -> (UName, Pi (PVar n))) <$> ident)
               <|> (UName,) . Pi <$> constant
    spaces
    void $ Tok.reservedOp tokenParser "->"
    spaces
    body <- topParse
    return $ PBind name pit body
    ) <?> "piLam"

var :: IParser (PExpr Name)
var = PVar <$> ident

constant :: IParser (PExpr Name)
constant = PConst <$> (try constVal <|> try (ConstTy <$> constTy))
                  <|> typeUniverse
    <?> "constant"

constVal :: IParser Const
constVal =
     try (ConstStr        <$> (char '\"' >> manyTill anyChar (char '\"')))
 <|> try (ConstFlt . read <$> many1 digit <++> string "." <++> many digit)
 <|>     (ConstInt . read <$> many1 digit)
 <?> "constVal"


constTy :: IParser ConstTy
constTy =
        try (IntTy <$ string "Int")
    <|> try (FltTy <$ string "Float")
    <|>     (StrTy <$ string "String")
    <?> "constTy"

typeUniverse :: IParser (PExpr Name)
typeUniverse = do
    Tok.reserved tokenParser "Type" >>
        ((spaces >> (PEType . read <$> many1 digit)) <|> return PIType)

typedIdent :: IParser (Name, PExpr Name)
typedIdent =
    (,) <$> ident <* (spaces >> char ':' >> spaces) <*> topParse
    <?> "typedIdent"

ident :: IParser Name
ident = SName <$> Tok.identifier tokenParser
    <?> "ident"

allOf :: IParser a -> IParser a
allOf p = p <* eof

test = parseTest (allOf topParse) "\\(whatever : Int) => 123.32 whatever"

ide = parseTest (allOf topParse)
    "\\(A : Type 0) => \\(f : A -> A) => \\(x : A) => f x"

paren :: IParser a -> IParser a
paren = between (char '(') (char ')')

infixr 5 <++>
(<++>) :: Monoid a => IParser a -> IParser a -> IParser a
(<++>) = liftA2 mappend
-}
