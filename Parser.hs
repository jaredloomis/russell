{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE TupleSections #-}
module Parser where

import Data.List
import Data.Monoid (Monoid(..))
import Control.Applicative hiding ((<|>), many)
import Data.Functor.Identity (runIdentity)
import Control.Monad.State
import Text.PrettyPrint.HughesPJClass (Pretty(..))

import Text.Parsec hiding (State)
import Text.Parsec.Pos (initialPos)
import qualified Text.Parsec.Token as Tok
import Text.Parsec.Language (emptyDef)

import qualified Data.Map as M

import Term
import Tactic

data PTerm n =
    PPar n
  | PApp (PTerm n) (PTerm n)
  | PBind n (Binder (PTerm n)) (PTerm n)
  | PConstant !Constant
  | PTypeI
  | PTypeE !Int
  deriving (Show, Eq, Functor)

type PEnv = [(Name, Binder (PTerm Name))]

type IParser a = ParsecT String () (State SourcePos) a

parsedToCore :: PEnv -> PTerm Name -> TypeCheck (Term Name)
parsedToCore env (PPar n)
    | holeName n = return $ Par Bound n (Type 0)
    | otherwise  =
        fmap (Par Bound n) . parsedToCore env
            =<< lookupName env mempty n -- TODO: What if it's a Ref?
parsedToCore env (PApp f x) =
    App <$> parsedToCore env f <*> parsedToCore env x
parsedToCore env (PBind n lam@(Lam ty) x) =
    Bind n . Lam
        <$> parsedToCore env ty
        <*> parsedToCore ((n, lam) : env) x
parsedToCore env (PBind n hole@(Hole ty) x) =
    Bind n . Hole
        <$> parsedToCore env ty
        <*> parsedToCore ((n, hole) : env) x
parsedToCore env (PBind n pi'@(Pi ty) x) =
    Bind n . Pi
        <$> parsedToCore env ty
        <*> parsedToCore ((n, pi') : env) x
parsedToCore env (PBind n lt@(Let ty val) x) = do
    lt' <- Let <$> parsedToCore env ty <*> parsedToCore env val
    Bind n lt' <$> parsedToCore ((n, lt) : env) x
parsedToCore _ (PConstant cnst) = return $ Constant cnst
parsedToCore _  PTypeI    = return $ Type 0  -- TODO
parsedToCore _ (PTypeE i) = return $ Type i

explicitHoles :: Term Name -> TypeCheck (Term Name)
explicitHoles x = do
    (x',(holes,_)) <- runStateT (explicitHoles' [] x) ([], 0)
    return $
        foldr (\(holeN, holeTy) b -> Bind holeN (Hole holeTy) b)
              x' holes

explicitHoles' ::
    [(Name, Binder (Term Name))] ->
    Term Name ->
    StateT ([(Name, Term Name)], Int) TypeCheck (Term Name)
explicitHoles' _ p@(Par nt n ty)
    | holeName n = Par nt <$> genName ty <*> return ty
    | otherwise  = return p
explicitHoles' env (App f x@(Par nt n _))
    | holeName n = do
        f' <- explicitHoles' env f
        tyF <- lift $ typeOf env mempty f' --TODO: CONTEXT
        case tyF of
            Bind _ (Pi tyN) _ ->
                App f' <$> (Par nt <$> genName tyN <*> return tyN)
            _ -> lift $ TypeError (NotAFunction f')
    | otherwise = App <$> explicitHoles' env f <*> return x
explicitHoles' env (App f x) =
    App <$> explicitHoles' env f <*> explicitHoles' env x
explicitHoles' env (Bind n (Lam ty) x) =
    let env' = (n,Lam ty):env
    in Bind n . Lam
            <$> explicitHoles' env' ty
            <*> explicitHoles' env' x
explicitHoles' env (Bind n (Hole ty) x) =
    let env' = (n,Hole ty):env
    in Bind n . Hole
            <$> explicitHoles' env' ty
            <*> explicitHoles' env' x
explicitHoles' env (Bind n (Pi ty) x) =
    let env' = (n,Pi ty):env
    in Bind n . Pi
            <$> explicitHoles' env' ty
            <*> explicitHoles' env' x
explicitHoles' env (Bind n (Let ty val) x) = do
    let env' = (n,Let ty val):env
    lt' <- Let
            <$> explicitHoles' env ty
            <*> explicitHoles' env' val

    Bind n lt'
            <$> explicitHoles' env' x
explicitHoles' _ c@Constant{} = return c
explicitHoles' _ t@Type{} = return t

genName :: Term Name -> StateT ([(Name, Term Name)], Int) TypeCheck Name
genName ty = do
    (n, i) <- get
    put (n, i+1)
    let name = SName $ "hole" ++ show i
    modify $ \(ns, i') -> ((name, ty) : ns, i')
    return name

holeName :: Name -> Bool
holeName (SName "_") = True
holeName (IName _ "_") = True
holeName _ = False

----------------
-- Def Parser --
----------------

parseContext :: IParser (Context (PTerm Name))
parseContext = MkContext . uncurry M.singleton <$> parseFuncDef

parseFuncDef :: IParser (Name, Def (PTerm Name))
parseFuncDef = do
    name <- lexeme identifier
    lexeme $ reservedOp ":"
    ty <- parseExpr

    checkIndent

    _name' <- lexeme identifier
    -- if name == name'
    lexeme $ reservedOp "="
    term <- sameOrIndented (lexeme parseExpr)

    return (name, Function ty term)

------------
-- Parser --
------------

iparse :: IParser a -> SourceName -> String -> Either ParseError a
iparse p n s = runIdentity .
    flip evalStateT (initialPos n) $ runParserT p () n s

tokenParser :: Tok.GenTokenParser String a (State SourcePos)
tokenParser =
    let tp = emptyDef {
        Tok.reservedOpNames = [":", "=", ":=", "\\", "|", "->", "=>"],
        Tok.reservedNames   = ["data", "where", "Type", "_"],

        Tok.commentStart    = "{-",
        Tok.commentEnd      = "-}",
        Tok.commentLine     = "--",
        Tok.nestedComments  = True,
        Tok.identStart      = letter,
        Tok.identLetter     = alphaNum <|> oneOf "_'",
        Tok.opStart         = oneOf ":!#$%&*+./<=>?@\\^|-~",
        Tok.opLetter        = Tok.opStart tp,
        Tok.caseSensitive   = True
        }
    in Tok.makeTokenParser tp

reservedOp :: String -> IParser ()
reservedOp = Tok.reservedOp tokenParser

reserved :: String -> IParser ()
reserved = Tok.reserved tokenParser

identifier :: IParser Name
identifier =
    SName <$> (try         (Tok.identifier tokenParser)
          <|>  try (parens (Tok.identifier tokenParser))
          <|>  try    (lexeme (string "_"))
          <|>  parens (lexeme (string "_")))
    <?> "identifier"

lexeme :: IParser a -> IParser a
lexeme = Tok.lexeme tokenParser

parens :: IParser a -> IParser a
parens = Tok.parens tokenParser

----
----

parseExpr :: IParser (PTerm Name)
parseExpr = try piLam <|> try lambda <|> try app <|> atom
    <?> "parseExpr"

app :: IParser (PTerm Name)
app = do
    foldl1' PApp <$> many1 (sameOrIndented $ lexeme atom) <?> "app"

atom :: IParser (PTerm Name)
atom = try constant <|> try var <|> parens parseExpr <?> "atom"

lambda :: IParser (PTerm Name)
lambda = (do
    reservedOp "\\"
    (name, ty) <- same . lexeme $
            try (parens typedIdent)
        <|>     ((,PPar "_") <$> identifier)
    sameOrIndented . lexeme $ reservedOp "=>"
    body <- sameOrIndented parseExpr
    return $ PBind name (Lam ty) body
    ) <?> "lambda"

piLam :: IParser (PTerm Name)
piLam = (do
    (name, pit) <-
            try ((\(n,t) -> (n, Pi t)) <$> lexeme (parens typedIdent))
        <|>     (SName "_",) . Pi <$> (try lambda <|> try app <|> atom)
    sameOrIndented . lexeme $ reservedOp "->"
    body <- sameOrIndented $ lexeme parseExpr
    return $ PBind name pit body
    ) <?> "piLam"

var :: IParser (PTerm Name)
var = PPar <$> identifier

constant :: IParser (PTerm Name)
constant = PConstant <$> (try constVal <|> try (ConstTy <$> constTy))
                     <|>  typeUniverse
    <?> "constant"

constVal :: IParser Constant
constVal =
     try (ConstStr               <$> Tok.stringLiteral tokenParser)
 <|> try (ConstFlt . realToFrac  <$> Tok.float         tokenParser)
 <|>     (ConstInt . fromInteger <$> Tok.integer       tokenParser)
 <?> "constVal"

constTy :: IParser ConstTy
constTy =
        try (IntTy <$ string "Int")
    <|> try (FltTy <$ string "Float")
    <|>     (StrTy <$ string "String")
    <?> "constTy"

typeUniverse :: IParser (PTerm Name)
typeUniverse = lexeme (reserved "Type") *>
    option PTypeI (PTypeE . read <$> sameOrIndented (many1 digit))

typedIdent :: IParser (Name, PTerm Name)
typedIdent =
    (,) <$> lexeme identifier <*  sameOrIndented (lexeme (char ':'))
                              <*> sameOrIndented (lexeme  parseExpr)
    <?> "typedIdent"

-------------------
-- Second Parser --
-------------------

parseContext' :: IParser (Context (PTerm Name))
parseContext' =
    MkContext . M.fromList <$> many (lexeme parseCoqDef)

parseCoqDef :: IParser (Name, Def (PTerm Name))
parseCoqDef = do
    -- Definition name.
    name <- lexeme identifier
    -- Typed, named args.
    args <- many (parens typedIdent)

    lexeme (reservedOp ":")

    -- Unnamed args / body type.
    tyBody <- parseExpr

    lexeme (reservedOp ":=")

    -- Definition body.
    term <- lexeme (sameOrIndented parseExpr)
    --term <- sameOrIndented (lexeme parseExpr)

        -- Total type, with Pis added for args.
    let tyTotal = addPis args tyBody
        -- Total term, with Lams added for args.
        termTotal = addLams args term

    return (name, Function tyTotal termTotal)

addLams :: [(Name, PTerm Name)] -> PTerm Name -> PTerm Name
addLams = flip . foldr $ uncurry ((. Lam) . PBind)

addPis :: [(Name, PTerm Name)] -> PTerm Name -> PTerm Name
addPis = flip . foldr $ uncurry ((. Pi) . PBind)

--------------------
-- Parser Helpers --
--------------------

sameOrIndented :: IParser a -> IParser a
sameOrIndented = (sameOrIndentCheck >>)

sameOrIndentCheck :: IParser ()
sameOrIndentCheck = checkSame <|> indent

indented :: IParser a -> IParser a
indented = (indent >>)

indent :: IParser ()
indent = do
    pos <- getPosition
    s <- get
    if sourceColumn pos <= sourceColumn s
        then parserFail "not indented"
    else put $ setSourceLine s (sourceLine pos)

same :: IParser a -> IParser a
same = (checkSame >>)

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

-------------
-- TESTING --
-------------

newP = case newParse of
    MkContext defMap -> case snd . head . M.toList $ defMap of
        Function ty term -> do
            tyC   <- parsedToCore [] ty
            termC <- parsedToCore [] term
            return (Function tyC termC)
        TyDecl n ty -> TyDecl n <$> parsedToCore [] ty

newP' = case newParse of
    MkContext defMap -> case snd . head . M.toList $ defMap of
        Function ty term -> do
            tyC   <- parsedToCore [] ty
            termC <- parsedToCore [] term
            return (tyC, termC)
        TyDecl _ ty -> do
            tyC <- parsedToCore [] ty
            return (tyC, error "axiom")

testNew = case newP' of
    PassCheck (ty, term) -> do
        print $ pPrint term
        putStr "    : "
        print $ pPrint ty
    _ -> return ()

newParseC = flip fmap newParse $ \x ->
    case parsedToCore [] x of
        PassCheck p -> p
        TypeError err -> error $ show err

newParse = parsef (allOf parseContext') "newParse" $
    "id (A : Type) (a : A) : A := a\n" ++
    "const (A : Type) (B : Type) (a : A) (b : B) : B := b\n" ++
    "aVal : Int := id Int (const Float Int 13.2 100)"

--

parsef p t s =
    let Right x = iparse p t s
    in x

testDef = iparse (allOf parseContext) "testDef" $
    "hello : Int\n"++
    "hello = (\\a => \\b => b) 12 13"
{-
    "id : (A : Type) -> A -> A\n"++
    "id = \\ty => \\a => a"
-}

testDef' =
    let Right (MkContext td) = testDef
        (Function ty fun) = snd . head . M.toList $ td

        PassCheck funC    = explicitHoles =<< parsedToCore [] fun
--        funCN             = normalize funC

        PassCheck tyC     = explicitHoles =<< parsedToCore [] ty
--        tyCN              = normalize tyC

        PassCheck tyCI    = explicitHoles =<< typeOf [] mempty funC
--        tyCIN             = normalize tyCI
    in do
        print $ tyCI
        let PassCheck s = unify [] tyC tyCI
        print s
        let tyCI' = applySubst (M.fromList s) tyCI
        return $ Function tyCI' funC

idp = parsef (allOf parseExpr) "idp" $
    "(\\(A : Type) => \\(a : A) => a) " ++
    "_ 123"

idpC = parsedToCore [] idp
idpC' = idpC >>= explicitHoles
idpCN = fmap normalize idpC'
tyIdp = fmap (typeOf [] mempty) idpCN

tenC' = fmap normalize tenC
tyTen = fmap (typeOf [] mempty) tenC
tenC  = parsedToCore [] ten

idC  = parsedToCore [] id'
tyId = fmap (typeOf [] mempty) idC

apps :: PTerm Name -> [PTerm Name] -> PTerm Name
apps = foldl' PApp

id' :: PTerm Name
id' = PBind "A" (Lam PTypeI) $
      PBind "a" (Lam (PPar "A")) $
      PPar "a"

ten :: PTerm Name
ten = apps id' [PConstant (ConstTy IntTy),
                PConstant (ConstInt 10)]

filled = do
    ty <- holeyT
    fill <- unify [] ty (Type 0)
    return $ foldr (\(n,r) x -> subst n r x) ty fill

holeyT = typeOf [] mempty =<< parsedToCore [] holey

holey :: PTerm Name
holey = PBind "ty" (Hole PTypeI) $
    apps id' [PPar "ty", PConstant (ConstTy IntTy)]

--holey = PBind "ty" (Hole PTypeI) $
--  apps id' [PPar "ty", PConstant (ConstInt 10)]
