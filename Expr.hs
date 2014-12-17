{-# LANGUAGE GADTs #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE TupleSections #-}
module Expr where

data Expr n =
    Par !NameType n --(Expr n)
  | Var !Int
  | App (Expr n) (Expr n)
  | Bind n (Binder (Expr n)) (Expr n)
  | Const !Const
  | Type !Int
  deriving (Show, Eq, Functor)

showExpr :: Show n => Expr n -> String
showExpr (Par _ n) = show n --"Par " ++ show ty ++ " " ++ show n
showExpr (Var i)    = "Var " ++ show i
showExpr (App f x)  = "(" ++ showExpr f ++ ") (" ++ showExpr x ++ ")"
showExpr (Bind n (Lam ty) b) =
    "\\(" ++ show n ++ " : " ++ showExpr ty ++ ") => " ++ showExpr b
showExpr (Bind n (Pi ty) b) =
    "(" ++ show n ++ " : " ++ showExpr ty ++ ") -> " ++ showExpr b
showExpr (Const c) = show c
showExpr (Type i) = "Type " ++ show i

data Binder b =
    Lam {binderTy :: b}
  | Pi  {binderTy :: b} --, binderKind :: b}
--  | Let {binderTy :: b, binderVal :: b}
  deriving (Show, Eq, Functor)

data Const =
    ConstInt !Int
  | ConstFlt !Float
  | ConstStr !String
  | ConstTy  !ConstTy
  deriving (Eq)

instance Show Const where
    show (ConstInt i) = show i
    show (ConstFlt f) = show f
    show (ConstStr s) = show s
    show (ConstTy  t) = show t

data ConstTy = IntTy | FltTy | StrTy
  deriving (Eq)

instance Show ConstTy where
    show IntTy = "Int"
    show FltTy = "Float"
    show StrTy = "String"

data Name =
    SName !String
  | IName !Int
  | UName
  deriving (Eq)

instance Show Name where
    show (SName s) = s
    show (IName i) = "IName@" ++ show i
    show UName     = "_"

data NameType =
    Bound
  | Ref
  | DataCon {ntTag :: !Int}
  | TypeCon {ntTag :: !Int}
  deriving (Show, Eq)

-------------------
-- Type checking --
-------------------

typeWith :: Eq n =>
    [(n, Expr n)] -> Expr n -> Either String (Expr n)
typeWith ctx e = case e of
    Type  i -> return $ Type (i+1)
    Const c -> return $ constType c
    Par _ x -> case lookup x ctx of
        Nothing -> Left "Unbound variable"
        Just a  -> return a
    Bind x (Lam a) b -> do
        b' <- typeWith ((x, a):ctx) b
        let p = Bind x (Pi a) b'
        _ <- typeWith ctx p
        return p
    Bind x (Pi a) b -> do
        eS <- fmap whnf (typeWith ctx a)
        s  <- case eS of
            Type i  -> return (Type i)
            _       -> Left "Invalid input type"
        let ctx' = (x, a):ctx
        eT <- fmap whnf (typeWith ctx' b)
        t  <- case eT of
            Type i  -> return (Type i)
            _       -> Left "Invalid output type"
        return $ maxType s t
    App f a  -> do
        e' <- fmap whnf (typeWith ctx f)
        (x, aa, b) <- case e' of
            Bind x (Pi aa) b -> return (x, aa, b)
            _          -> Left "Not a function"
        aa' <- typeWith ctx a
        let nf_A  = normalize aa
            nf_A' = normalize aa'
        if nf_A == nf_A'
            then return (subst x a b)
            else Left "Type mismatch"
    Var _ -> Left "Can't typecheck 'Var's"

constType :: Const -> Expr n
constType ConstInt{} = Const (ConstTy IntTy)
constType ConstFlt{} = Const (ConstTy FltTy)
constType ConstStr{} = Const (ConstTy StrTy)
constType ConstTy{}  = Type 0

maxType :: Expr n -> Expr n -> Expr n
maxType (Type i) (Type j)
    | i >= j    = Type i
    | otherwise = Type j
maxType _ _ = error "maxType given something other than 'Type'."

------------------------
-- Operations on Expr --
------------------------

-- | Reduce an expression to weak-head normal form
whnf :: Eq n => Expr n -> Expr n
whnf e = case e of
    App f a -> case whnf f of
        Bind x (Lam _A) b -> whnf (subst x a b)  -- Beta reduce
        _          -> e
    _       -> e

normalize :: Eq n => Expr n -> Expr n
normalize e = case e of
    Bind x (Lam _A) b -> case b' of
        App f a -> case a of
            Par _ x' | x == x' && not (x `freeIn` f) -> f  -- Eta reduce
                     | otherwise                     -> e'
            _                                        -> e'
        _       -> e'
      where
        b' = normalize b
        e' = Bind x (Lam (normalize _A)) b'
    Bind x (Pi _A) b -> Bind x (Pi  (normalize _A)) (normalize b)
    App f _C   -> case normalize f of
        Bind x (Lam _A) _B -> normalize (subst x _C _B)  -- Beta reduce
        f'          -> App f' (normalize _C)
    Par _ _    -> e
    Const _    -> e
    Type _     -> e
    Var _      -> e

-- | Returns whether a variable is free in an expression
freeIn :: Eq n => n -> Expr n -> Bool
freeIn x = go
  where
    go e = case e of
        Bind x' (Lam a) b -> x /= x' && (go a || go b)
        Bind x' (Pi  a) b -> x /= x' && (go a || go b)
        Par _ x'    -> x == x'
        App f a     -> go f || go a
        Const _     -> False
        Type  _     -> False
        Var   _     -> False

substEnv :: Eq n => [(n, Expr n)] -> Expr n -> Expr n
substEnv ctx expr = foldr (uncurry subst) expr ctx

subst :: Eq n => n -> Expr n -> Expr n -> Expr n
subst x0 e0 = go
  where
    go e = case e of
        Bind x (Lam a) b -> helper Lam x a b
        Bind x (Pi  a) b -> helper Pi  x a b
        App f a    -> App (go f) (go a)
        Par _ x    -> if x == x0 then e0 else e
        Const _    -> e
        Type  _    -> e
        Var   _    -> e

    helper c x a b =
        if x == x0
            then Bind x (c a) b  -- x shadows x0
        else
            Bind x (c (go a)) (go (subst x (Par Ref x) b))
{-
            let fs = IntSet.union (freeOf txt (Var x0)) (freeOf txt e0)
            in  if IntSet.member n fs
                then
                    let x' = V txt (IntSet.findMax fs + 1)
                    in  c x' (go _A) (go (subst x (Var x') b))
                else c x (go _A) (go b)
-}
