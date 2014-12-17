{-# LANGUAGE DeriveFunctor #-}
module Decl where

import Expr

data PDecl t =
    Caf Name t t
  | Data (PData t)
  deriving (Eq, Functor)

instance Show t => Show (PDecl t) where
    show (Caf name ex ty) = show name ++ " : " ++ show ty ++ "\n" ++
                            show name ++ " = " ++ show ex
    show (Data pdata)  = show pdata

data PData t = PDataDecl Name t [(Name, t)]
  deriving (Eq, Functor)

instance Show t => Show (PData t) where
    show (PDataDecl tyName tyTy cons) =
        "data " ++ show tyName ++ " : " ++ show tyTy ++ " where\n" ++
        concatMap showCon cons
      where
        showCon (conName, conTy) = "    " ++
            show conName ++ " : " ++ show conTy ++ "\n"

declTypes :: Eq n => PDecl (Expr n) -> [(Name, Expr n)]
declTypes (Caf name _ ty) = [(name, ty)]
declTypes (Data (PDataDecl tyName tyTy cons)) =
    (tyName, tyTy) : cons

right :: Either a b -> b
right (Right r) = r
right (Left _) = error "Decl.right: recieved left."

declNames :: PDecl (Expr n) -> [(Name, Expr n)]
declNames (Caf name expr _) = [(name, expr)]
declNames _                 = []
--declNames (Data (PDataDecl tyName tyTy cons)) =
--    (tyName, tyTy) : cons

typeWith' :: [PDecl (Expr Name)] -> Expr Name -> Either String (Expr Name)
typeWith' decls = typeWith (concatMap declTypes decls)
