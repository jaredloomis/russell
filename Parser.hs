{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE TupleSections #-}
module Parser where

import Data.List
import Data.Monoid (Monoid(..))
import Control.Applicative hiding ((<|>), many)
import Data.Functor.Identity (runIdentity)
import Control.Monad.State
import Control.Arrow hiding (app)

import Text.Parsec hiding (State)
import Text.Parsec.Pos (initialPos)
import qualified Text.Parsec.Token as Tok
import Text.Parsec.Language (emptyDef)

import qualified Data.Map as M

import Term
--import Tactic

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


parsedCtxToCore ::
    PEnv ->
    Context (PTerm Name) ->
    TypeCheck (Context (Term Name))
parsedCtxToCore env ctx@(MkContext defMap) = do
    MkContext . M.fromList <$> parsedCtxToCore' (M.toList defMap)
  where
    parsedCtxToCore' ::
        [(Name, Def (PTerm Name))] ->
        TypeCheck [(Name, Def (Term Name))]
    parsedCtxToCore' ((n, Function ty term) : xs) = do
        xs' <- parsedCtxToCore' xs
        ty'   <- parsedToCore env ctx ty
        term' <- parsedToCore env ctx term
        return $ (n, Function ty' term') : xs'
    parsedCtxToCore' ((n, TyDecl nt ty) : xs) = do
        xs' <- parsedCtxToCore' xs
        ty' <- parsedToCore env ctx ty
        return $ (n, TyDecl nt ty') : xs'
    parsedCtxToCore' [] = return []

parsedToCore ::
    PEnv ->
    Context (PTerm Name) ->
    PTerm Name ->
    TypeCheck (Term Name)
parsedToCore env ctx (PPar n)
    | holeName n = return $ Par Bound n (Type 0)
    | otherwise  =
        fmap (Par Bound n) . parsedToCore env ctx
            =<< lookupName env ctx n -- TODO: What if it's a Ref?
parsedToCore env ctx (PApp f x) =
    App <$> parsedToCore env ctx f <*> parsedToCore env ctx x
parsedToCore env ctx (PBind n lam@(Lam ty) x) =
    Bind n . Lam
        <$> parsedToCore env ctx ty
        <*> parsedToCore ((n, lam) : env) ctx x
parsedToCore env ctx (PBind n hole@(Hole ty) x) =
    Bind n . Hole
        <$> parsedToCore env ctx ty
        <*> parsedToCore ((n, hole) : env) ctx x
parsedToCore env ctx (PBind n pi'@(Pi ty) x) =
    Bind n . Pi
        <$> parsedToCore env ctx ty
        <*> parsedToCore ((n, pi') : env) ctx x
parsedToCore env ctx (PBind n lt@(Let ty val) x) = do
    lt' <- Let <$> parsedToCore env ctx ty <*> parsedToCore env ctx val
    Bind n lt' <$> parsedToCore ((n, lt) : env) ctx x
parsedToCore _ _ (PConstant cnst) = return $ Constant cnst
parsedToCore _ _  PTypeI    = return $ Type 0  -- TODO
parsedToCore _ _ (PTypeE i) = return $ Type i

{-
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
-}

explicitHoles :: Term Name -> Context (Term Name) -> TypeCheck (Term Name)
explicitHoles x ctx = do
    (x',(holes,_)) <- runStateT (explicitHoles' [] ctx x) ([], 0)
    return $
        foldr (\(holeN, holeTy) b -> Bind holeN (Hole holeTy) b)
              x' holes

explicitHoles' ::
    [(Name, Binder (Term Name))] ->
    Context (Term Name) ->
    Term Name ->
    StateT ([(Name, Term Name)], Int) TypeCheck (Term Name)
explicitHoles' _ _ p@(Par nt n ty)
    | holeName n = Par nt <$> genName ty <*> return ty
    | otherwise  = return p
explicitHoles' env ctx (App f x@(Par nt n _))
    | holeName n = do
        f' <- explicitHoles' env ctx f
        tyF <- lift $ typeOf env ctx f'
        case tyF of
            Bind _ (Pi tyN) _ ->
                App f' <$> (Par nt <$> genName tyN <*> return tyN)
            _ -> lift $ TypeError (NotAFunction f')
    | otherwise = App <$> explicitHoles' env ctx f <*> return x
explicitHoles' env ctx (App f x) =
    App <$> explicitHoles' env ctx f <*> explicitHoles' env ctx x
explicitHoles' env ctx (Bind n (Lam ty) x) =
    let env' = (n,Lam ty):env
    in Bind n . Lam
            <$> explicitHoles' env' ctx ty
            <*> explicitHoles' env' ctx x
explicitHoles' env ctx (Bind n (Hole ty) x) =
    let env' = (n,Hole ty):env
    in Bind n . Hole
            <$> explicitHoles' env' ctx ty
            <*> explicitHoles' env' ctx x
explicitHoles' env ctx (Bind n (Pi ty) x) =
    let env' = (n,Pi ty):env
    in Bind n . Pi
            <$> explicitHoles' env' ctx ty
            <*> explicitHoles' env' ctx x
explicitHoles' env ctx (Bind n (Let ty val) x) = do
    let env' = (n,Let ty val):env
    lt' <- Let
            <$> explicitHoles' env ctx ty
            <*> explicitHoles' env' ctx val

    Bind n lt'
            <$> explicitHoles' env' ctx x
explicitHoles' _ _ c@Constant{} = return c
explicitHoles' _ _ t@Type{} = return t

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
parseContext =
      try (MkContext . uncurry M.singleton <$> parseFuncDef)
  <|> parseDataDecl

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

-----------------------------
-- Data declaration parser --
-----------------------------

parseDataDecl :: IParser (Context (PTerm Name))
parseDataDecl = do
    lexeme (reserved "data")
    (tyName, ty) <- lexeme typedIdent
    lexeme (reserved "where")

    constrs <- map (id *** TyDecl (DataCon 0)) <$> block (typedIdent)

    return . MkContext . M.fromList $ (tyName, TyDecl (TypeCon 0) ty) : constrs

-------------------
-- Second Parser --
-------------------

parseContext' :: IParser (Context (PTerm Name))
parseContext' = fmap mconcat . many $
    try parseDataDecl <|> parseCoqCtx

parseCoqCtx :: IParser (Context (PTerm Name))
parseCoqCtx = MkContext . uncurry M.singleton <$> lexeme parseCoqDef

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

parsef p t s =
    let Right x = iparse p t s
    in x

--

testParseC = do
    npc@(MkContext npcm) <- newParseC
    let val = head $ M.toList npcm
    case val of
        (_, Function _ term) -> return $ substCtx term npc
        _ -> undefined
--    return . head $ M.toList npcm

newParseC = parsedCtxToCore [] newParse

newParse = parsef (allOf parseContext') "newParse" $
    "id (A : Type) (a : A) : A := a\n" ++
    "const (A : Type) (B : Type) (a : A) (b : B) : B := b\n" ++
    "aVal : Int := id _ (const _ _ 13.2 100)"
