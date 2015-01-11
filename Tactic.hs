{-# LANGUAGE DeriveFunctor #-}
module Tactic where

import Control.Monad.State
import Data.Monoid

import qualified Data.Map as M

import Term

{-
type Cogito a = StateT CState TypeCheck a

data CState = CState {
    cogCtx :: Context (Term Name)
    } deriving (Show, Eq)
-}

-----------
-- Proof --
-----------

data ProofState = ProofState {
    proofTerm    :: ProofTerm,
--    proofType    :: Term Name,
    proofHoles   :: [Name],
    proofContext :: Context (Term Name),
    psNameSeed   :: Int
    } deriving (Show, Eq)

data ProofTerm = ProofTerm {
    ptTerm    :: Term Name,
    ptEnv     :: Env,
    ptUpdates :: [(Name, Term Name)]
    } deriving (Show, Eq)

-----------
-----------

-- TODO
infer :: Term Name -> Term Name -> TypeCheck (Term Name)
infer term ty = do
    tyI <- typeOf [] mempty term
    s <- unify [] tyI ty
    return $ foldr (\(n,r) x -> subst n r x) tyI s

-----------------
-- Unification --
-----------------

unify :: Env -> Term Name -> Term Name -> TypeCheck [(Name, Term Name)]
unify _ x y | x == y = return []
unify _ Type{} Type{} = return []
unify _ Constant{} Constant{} = return [] -- XXX
unify _ (Par _ n _) b
    | pureTerm b = return [(n, b)]
unify _ a (Par _ n _)
    | pureTerm a = return [(n, a)]
unify env (Bind _ ba aa) (Bind _ bb ab)
    | sameBinder ba bb = do
        ub <- unifyBind env ba bb
        ua <- unify env aa ab
        return $ ub ++ ua
  where
    sameBinder Lam{} Lam{} = True
    sameBinder Pi{}  Pi{}  = True
    sameBinder _     _     = False
unify env (App f x) (App g y) = do
    uf <- unify env f g
    ux <- unify env x y
    return $ uf ++ ux
unify _ _ _ = return []

unifyBind ::
    Env ->
    Binder (Term Name) -> Binder (Term Name) ->
    TypeCheck [(Name, Term Name)]
unifyBind env (Let tx vx) (Let ty vy) = do
    ut <- unify env tx ty
    uv <- unify env vx vy
    return $ ut ++ uv
unifyBind env (Lam  tx) (Lam  ty) = unify env tx ty
unifyBind env (Pi   tx) (Pi   ty) = unify env tx ty
unifyBind env (Hole tx) (Hole ty) = unify env tx ty
unifyBind _ _ _ = return []

{-
fillHoles :: Term Name -> Term Name -> StateT [(Name, Name)] TypeCheck Subst
fillHoles ty term = return M.empty
fillHoles _ Type{} = return M.empty
fillHoles _ Constant{} = return M.empty
fillHoles (Bind n (Pi nTy) tyB) (Bind m (Lam mTy) termB) =
    fillHoles tyB termB
-}
