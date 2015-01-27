{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
module Tactic where

import Prelude hiding (mapM_)
import Data.List
import Data.Maybe
import Data.Monoid
import Control.Applicative
import Control.Arrow
import Control.Monad.State hiding (mapM_)
import Data.Foldable (mapM_)
import Data.Traversable (traverse)
import Debug.Trace (trace)

import Text.PrettyPrint.HughesPJClass hiding ((<>))

import Term hiding (normalize, subst)
import qualified Term as T
import Parser

data ProofState = ProofState {
    proofName    :: Name,
    proofTerm    :: ProofTerm,
    -- ^ Current proof term
    proofType    :: Term Name,
    -- ^ Original goal
    proofHoles   :: [Name],
    unified      :: (Name, [(Name, Term Name)]),
    unsolved     :: [(Env, (Term Name, Term Name))],
    proofContext :: Context (Term Name),
    psNameSeed   :: Int
    } deriving (Show, Eq)

instance Pretty ProofState where
    pPrint (ProofState n tm ty hs (un, unif) prob _ctx _) =
        "==== " <> pPrint n <> " ====\n" <>
        pPrint tm <> "\n== Goal ==\n" <> pPrint ty <>
        "\n== Holes ==\n" <> "[" <> printHoles hs <> "]" <>
        "\n== Unified ==\n" <> pPrint un <> "\n" <> printUnified unif <>
        "\n== Problems ==\n" <> printProbs prob
      where
        printUnified ((n',t) : xs) =
            pPrint n' <> " ~=~ " <> pPrint t <> "\n" <>
            printUnified xs
        printUnified [] = ""

        printHoles (x : y : xs) = pPrint x <> ", " <> printHoles (y : xs)
        printHoles [x]          = pPrint x
        printHoles []           = ""

        printProbs ((_, (a, b)) : y : xs) =
            pPrint a <> " =?= " <> pPrint b <> "\n" <>
            printProbs (y : xs)
        printProbs [(_, (a, b))] =
            pPrint a <> " =?= " <> pPrint b
        printProbs [] = ""

data ProofTerm = ProofTerm {
    ptTerm    :: Term Name,
    ptEnv     :: Env
    } deriving (Show, Eq)

instance Pretty ProofTerm where
    pPrint (ProofTerm tm env) =
        "== Assumptions ==\n" <> printEnv env <>
        "\n== Term ==\n" <> pPrint tm
      where
        printEnv ((n, b) : xs) =
            pPrint n <> " : " <> pPrint (binderTy b) <>
            "\n" <> printEnv xs
        printEnv []       = ""

type Elab a = StateT ProofState TypeCheck a

type Tactic = Env -> Context (Term Name) ->
              Term Name -> Elab (Term Name)

------------------
-- Elab actions --
------------------

nameSeed :: Elab Int
nameSeed = do
    i <- gets psNameSeed
    modify $ \ps -> ps{psNameSeed = i+1}
    return i

getName :: String -> Elab Name
getName str = do
    i <- nameSeed
    return $ IName i str

focus :: Name -> Tactic
focus n _ _ t = do
    modify $ \ps ->
        let hs = proofHoles ps
        in if n `elem` hs
            then ps{proofHoles = n : (hs \\ [n])}
            else ps
    return t

unfocus :: Elab ()
unfocus = modify $ \ps ->
    let hs = proofHoles ps
    in case hs of
        []       -> ps
        (h : hs') -> ps{proofHoles = hs' ++ [h]}

newHole :: Name -> Elab ()
newHole (IName _ n) = do
    i <- nameSeed
    modify $ \ps ->
        let hs = proofHoles ps
        in ps{proofHoles = IName i n : hs}
newHole (SName n) = do
    i <- nameSeed
    modify $ \ps ->
        let hs = proofHoles ps
        in ps{proofHoles = IName i n : hs}

nextHole :: Elab (Maybe Name)
nextHole = gets (listToMaybe . proofHoles)

removeHole :: Maybe Name -> Elab ()
removeHole (Just n) = modify $ \ps ->
    ps{proofHoles = proofHoles ps \\ [n]}
removeHole Nothing = modify $ \ps ->
    ps{proofHoles = tail (proofHoles ps)}

newProof :: Name -> Context (Term Name) -> Term Name -> ProofState
newProof n ctx ty =
    let h = IName 0 "hole"
    in ProofState n
        (ProofTerm (Bind h (Hole ty) (Var Bound h ty)) [])
        ty
        [h] ("asdf",[]) [] ctx 1

check :: Env -> Term Name -> Elab (Term Name)
check env term = do
    ctx <- gets proofContext
    -- XXX: Should I use the current term's env,
    --      instead of requiring an explicit arg?
    --env <- gets (ptEnv . proofTerm)

    lift $ typeOf env ctx term

convert :: Env -> Term Name -> Term Name -> Elab ()
convert env x y =
    -- XXX: Should I use the current term's env,
    --      instead of requiring an explicit arg?
    --env <- gets (ptEnv . proofTerm)
    lift $ converts env x y

normalize :: Term Name -> Elab (Term Name)
normalize term = return $ T.normalize term
--    XXX:
--    ctx <- gets proofContext
--    return $ substCtx ctx (T.normalize term)

subst :: Name -> Term Name -> Tactic
subst n val _ _ term = do
    -- XXX?
    modify $ \ps -> ps{proofHoles = (proofHoles ps) \\ [n]}

    -- XXX?
    modify $ \ps ->
        let ProofTerm pt env = proofTerm ps
            env' = map (second $ fmap (T.subst n val)) env
        in ps{proofTerm = ProofTerm pt env'}

    let term'  = T.subst n val term
    return term'
{- modify $ \ps ->
    let ProofTerm pt env  = proofTerm ps
        pt'  = T.subst n term pt
        env' = map (second $ fmap (T.subst n term)) env

        hs   = proofHoles ps
        hs'  = hs \\ [n]
    in ps{proofTerm = ProofTerm pt' env', proofHoles = hs'}
-}

substProblems :: Name -> Term Name -> Elab ()
substProblems n term = modify $ \ps ->
    let probs = unsolved ps
        subst' = T.subst n term
        substProb =
            map (second $ fmap subst') *** (subst' *** subst')
        probs' = map substProb probs
    in ps{unsolved = probs'}

claim :: Name -> Term Name -> Tactic
claim n ty _ _ term = do
    modify $ \ps ->
        let hs = proofHoles ps
        in case hs of
            []     -> ps{proofHoles = [n]}
            (g : gs) -> ps{proofHoles = g : n : gs}
    return $ Bind n (Hole ty) term
{-
    -- Create a Hole, remember the hole that was first.
    mh <- nextHole
    newHole n

    -- Set focus back on the original first hole.
    mapM_ focus mh

    return $ Bind n (Hole ty) term
-}

fill :: Term Name -> Tactic
fill guess env ctx (Bind n (Hole ty) e) = do
    tyG <- lift $ typeOf env ctx guess
    unify env ty tyG
    return $ Bind n (Guess ty guess) e
fill _ _ _ _ = lift . TypeError . Msg $ "Can't fill here."

solve :: Tactic
solve _ _ (Bind n (Guess _ val) e)
    | pureTerm val = do
        removeHole (Just n)
        return $ T.subst n val e
solve _ _ _ = do
    traceState
    lift . TypeError . Msg $ "Can't solve here."

attack :: Tactic
attack _ _ (Bind n (Hole ty) s) = do
    h <- getName "hole"
    modify $ \ps -> ps{proofHoles = h : proofHoles ps}

    let tm = Bind h (Hole ty) (Var Bound h ty)
    return $ Bind n (Guess ty tm) s
attack _ _ _ = lift . TypeError . Msg $ "Not an attackable hole."

try :: Tactic -> Tactic -> Tactic
try t1 t2 env ctx term =
    tryE (t1 env ctx term) (t2 env ctx term)

tryE :: Elab a -> Elab a -> Elab a
tryE e1 e2 = do
    pt <- get
    case runStateT e1 pt of
        PassCheck (x, st) -> put st >> return x
        TypeError _       -> e2

tacticN :: Tactic -> Elab ()
tacticN = tactic Nothing

tactic :: Maybe Name -> Tactic -> Elab ()
tactic (Just h) tac = do
    ps <- get
    pterm' <- tactic' [] (proofContext ps) (ptTerm $ proofTerm ps)

    modify $ \ps' -> ps'{proofTerm = (proofTerm ps'){ptTerm = pterm'}}
  where
    tactic' :: Env -> Context (Term Name) ->
            Term Name -> Elab (Term Name)
    tactic' env ctx tm@(Bind n b e)
        | holeB b && h == n = tac env ctx tm
        | otherwise = do
            b' <- tacticB env ctx b
            e' <- tactic' ((n, b') : env) ctx e
            return $ Bind n b' e'
    tactic' env ctx (App f a) =
        App <$> tactic' env ctx f
            <*> tactic' env ctx a
    tactic' _ _ tm = return tm

    tacticB ::
        Env -> Context (Term Name) ->
        Binder (Term Name) -> Elab (Binder (Term Name))
    tacticB env ctx = traverse (tactic' env ctx)

    holeB Hole{}  = True
    holeB Guess{} = True
    holeB _       = False
tactic Nothing tac = do
    mh <- nextHole
    case mh of
        Just _  -> tactic mh tac
        Nothing ->
            lift . TypeError . Msg $
                "Tactic applied on empty hole queue."
{-
tactic :: Maybe Name -> Tactic -> Elab ()
tactic (Just h) tac = do
    ps <- get
    pterm' <- tactic' [] (proofContext ps) (ptTerm $ proofTerm ps)

    modify $ \ps' -> ps'{proofTerm = (proofTerm ps'){ptTerm = pterm'}}
  where
    tactic' :: Env -> Context (Term Name) ->
            Term Name -> Elab (Term Name)
    tactic' env ctx tm@(Bind n (Guess ty val) e)
        | n == h    = tac env ctx tm
        | otherwise = do
            val' <- tactic' env ctx val
            ty'  <- tactic' env ctx ty
            Bind n (Guess ty' val') <$>
                tactic' ((n, Guess ty' val') : env) ctx e
    tactic' env ctx tm@(Bind n (Hole ty) e)
        | n == h    = tac env ctx tm
        | otherwise = do
            ty' <- tactic' env ctx ty
            Bind n (Hole ty') <$>
                tactic' ((n, Hole ty') : env) ctx e
    tactic' env ctx (Bind n (Lam ty) e) = do
        ty' <- tactic' env ctx ty
        Bind n (Lam ty') <$>
            tactic' ((n, Lam ty') : env) ctx e
    tactic' env ctx (Bind n (Pi ty) e) = do
        ty' <- tactic' env ctx ty
        Bind n (Pi ty') <$>
            tactic' ((n, Pi ty') : env) ctx e
    tactic' env ctx (Bind n (Let ty val) e) = do
        val' <- tactic' env ctx val
        ty'  <- tactic' env ctx ty
        Bind n (Let ty' val') <$>
            tactic' ((n, Let ty' val') : env) ctx e
    tactic' env ctx (App f a) =
        App <$> tactic' env ctx f
            <*> tactic' env ctx a
    tactic' _ _ tm = return tm
tactic Nothing tac = do
    mh <- nextHole
    case mh of
        Just _  -> tactic mh tac
        Nothing ->
            lift . TypeError . Msg $
                "Tactic applied on empty hole queue."
-}

forall :: Name -> Term Name -> Tactic
forall n ty env _ (Bind x (Hole t) (Var _ x' _)) | x == x' = do
    ctx <- gets proofContext
    tyT <- lift $ typeOf env ctx ty
    unify env tyT (Type 0)
    unify env t (Type 0)
    return $ Bind n (Pi ty) $ Bind x (Hole t) (Var Bound x t)
forall _ _ _ _ _ = lift . TypeError . Msg $ "Can't pi bind here."

intro :: Maybe Name -> Tactic
intro mn _ _ (Bind x (Hole t) (Var _ x' _)) | x == x' =
    let n  = fromMaybe x mn
        t' = case t  of
            Bind _ Pi{} _ -> t
            _ -> whnf t  -- TODO should be hnf, not whnf
    in case t' of
        Bind y (Pi s) tt ->
            let tt' = T.subst y (Var Bound n s) tt
            in return $ Bind n (Lam s) $ Bind x (Hole tt') $
                        Var Bound x tt'
        _ -> lift . TypeError . Msg $ "Can't introduce term."
intro _ _ _ _ = lift . TypeError . Msg $ "Can't introduce here."

letbind :: Name -> Term Name -> Term Name -> Tactic
letbind n ty val _ _ (Bind x (Hole t) (Var _ x' _)) | x == x' =
    return $ Bind n (Let ty val) $ Bind x (Hole t) (Var Bound x t)
letbind _ _ _ _ _ _ =
    lift . TypeError . Msg $ "Can't let bind here."

movelast :: Name -> Tactic
movelast n _ _ t = do
    modify $ \ps ->
        let hs = proofHoles ps
        in if n `elem` hs
            then ps{proofHoles = (hs \\ [n]) ++ [n]}
            else ps

    return t

prepFill :: Name -> [Name] -> Tactic
prepFill f as _ _ (Bind n (Hole ty) e) =
    let val = foldr (flip App) (Var Ref f $ Type 0) $
                            -- ^ XXX: The 'Type 0' should be 'Erased'
                map (\a -> Var Ref a $ Type 0) as
                            -- ^ XXX: The 'Type 0' should be 'Erased'
    in return $ Bind n (Guess ty val) e
prepFill _ _ _ _ _ = lift . TypeError . Msg $ "Can't prepare fill here."

completeFill :: Tactic
completeFill env ctx b@(Bind _ (Guess ty val) _) = do
    ty' <- lift $ typeOf env ctx val
    unify env ty ty'
    return b
completeFill _ _ _ = lift . TypeError . Msg $ "Can't complete fill here."

endUnify :: Tactic
endUnify _ _ term = do
    (_h, us) <- gets unified
--    modify $ \ps -> ps{unified = (h, [])}
    return $ foldr (uncurry T.subst) term us

dropHoles :: Elab ()
dropHoles = do
    pt <- gets (ptTerm . proofTerm)
    modify $ \ps ->
        ps{proofTerm = (proofTerm ps){ptTerm = dropHoles' pt}}
  where
    dropHoles' :: Term Name -> Term Name
    dropHoles' (App f x) = App (dropHoles' f) (dropHoles' x)
    dropHoles' (Bind n b e)
        | isHole b =
            let e' = dropHoles' e
            in if n `freeIn` e'
                then e'
                else Bind n (fmap dropHoles' b) e'
        | otherwise = Bind n (fmap dropHoles' b) (dropHoles' e)
    dropHoles' tm = tm

    isHole Hole{}  = True
    isHole Guess{} = True
    isHole _       = False

-----------------
-- Unification --
-----------------

unify :: Env -> Term Name -> Term Name -> Elab ()
unify env x y = do
    s <- primUnify env x y
    modify $ \ps ->
        let (n, us) = unified ps
        in ps{unified = (n, us ++ s)}
    mapM_ (\(n,t) -> tacticN (subst n t) >> substProblems n t) s
    reunify

reunify :: Elab ()
reunify = do
    probs <- gets unsolved
    ss <- mapM (\(env, (x, y)) -> primUnify env x y) probs
    mapM_ (tacticN . uncurry subst) (concat ss)

primUnify :: Env -> Term Name -> Term Name -> Elab [(Name, Term Name)]
primUnify _ x y | x == y = return []
primUnify _ Type{} Type{} = return []
primUnify env cx@(Constant x) cy@(Constant y)
    | x == y    = return []
    | otherwise = unifyTmpFail env cx cy
primUnify env a@(Var _ n _) b
    | pureTerm b && isHoleIn env n = return [(n, b)]
    | otherwise = unifyTmpFail env a b
primUnify env a b@(Var _ n _)
    | pureTerm a && isHoleIn env n = return [(n, a)]
    | otherwise = unifyTmpFail env a b
primUnify env a@(Bind _ Hole{} _) b = unifyTmpFail env a b
primUnify env a b@(Bind _ Hole{} _) = unifyTmpFail env a b
primUnify env (Bind _ ba aa) (Bind _ bb ab)
    | sameBinder ba bb = do
        ub <- unifyBind env ba bb
        ua <- primUnify env aa ab
        return $ composeSubst ub ua
  where
    sameBinder Lam{} Lam{} = True
    sameBinder Pi{}  Pi{}  = True
    sameBinder _     _     = False
primUnify env (App f x) (App g y) = do
    uf <- primUnify env f g
    ux <- primUnify env x y
    return $ composeSubst uf ux
primUnify env x y = unifyTmpFail env x y

unifyBind ::
    Env ->
    Binder (Term Name) -> Binder (Term Name) ->
    Elab [(Name, Term Name)]
unifyBind env (Let tx vx) (Let ty vy) = do
    ut <- primUnify env tx ty
    uv <- primUnify env vx vy
    return $ composeSubst ut uv
unifyBind env (Lam  tx) (Lam  ty) = primUnify env tx ty
unifyBind env (Pi   tx) (Pi   ty) = primUnify env tx ty
unifyBind env (Hole tx) (Hole ty) = primUnify env tx ty
unifyBind _ _ _ = return []

unifyFail :: Env -> Term Name -> Term Name -> Elab a
unifyFail env x y = do
    ps <- get
    let fs = unsolved ps
    put ps{unsolved = (env, (x, y)) : fs}
    lift $ TypeError (CantUnify x y)

unifyTmpFail :: Env -> Term Name -> Term Name -> Elab [(Name, Term Name)]
unifyTmpFail env x y = do
    ps <- get
    let fs = unsolved ps
    put ps{unsolved = (env, (x, y)) : fs}
    return []

composeSubst :: Subst -> Subst -> Subst
composeSubst s1 s2 =
    unionBy (\(n,_) (n',_) -> n == n')
        (map (second $ applySubst s1) s2) s1

-----------------
-- Elaboration --
-----------------

elab :: PTerm Name -> Elab ()
elab (PVar n) = do
    pTy <- gets proofType
    tacticN $ fill (Var Bound n pTy)
    tacticN   solve
elab (PConstant c) = do
    tacticN $ fill (Constant c)
    tacticN   solve
elab Placeholder = unfocus
elab (PLam n e) = do
    checkPiGoal n
    tacticN   attack
    tacticN $ intro (Just n)
    elab e
    tacticN solve
elab (PBind n Lam{} e) =
    -- TODO
    elab $ PLam n e
elab (PBind n (Pi tyN) e) = do
    tacticN   attack
    xTy <- getName "hole"

    tacticN $ claim xTy (Type 0)
    tacticN $ forall n (Var Bound xTy (Type 0))
    tacticN $ focus xTy

    elab tyN
    elab e
    tacticN solve
elab (PLet n val e) = do
    tacticN attack
    xTy <- getName "hole"
    vTy <- getName "hole"

    tacticN $ claim xTy (Type 0)
    tacticN $ claim vTy (Var Bound xTy (Type 0))

    tacticN $ letbind n
        (Var Bound xTy (Type 0))
        (Var Bound vTy (Var Bound xTy (Type 0)))

    tacticN $ focus vTy
    elab val
    elab e
    tacticN solve
elab (PBind n (Let _ val) e) =
    -- TODO
    elab $ PLet n val e
elab tm@PApp{} = do
    -- Collect all args and find the base function
    -- they are all being applied to.
    let (f, args) = toFunc tm

    -- Claim a name for each argument, and for each argument's type.
    (argNames, argTyNames) <- fmap unzip . (flip mapM) args $ \_arg -> do
        atN <- getName "argTy"
        tacticN $ claim atN (Type 0)

        aN <- getName "aElab"
        tacticN $ claim aN (Var Bound atN (Type 0))
        return (aN, atN)

    -- Claim a name for the result type of the function.
    -- ie, f : ... -> resultTy
    resultTy <- getName "resTy"
    tacticN $ claim resultTy (Type 0)

    -- The complete type of the function is
    -- 'args -> resultTy'
    let tyFN = foldr (\x b ->
                Bind "_" (Pi $ Var Bound x (Type 0)) b)
            (Var Bound resultTy (Type 0))
            argTyNames

    fN <- getName "fElab"
    tacticN $ claim fN tyFN

    -- Prepfill args.
    tacticN $ prepFill fN argNames

    -- Elab function.
    tacticN $ focus fN
    elab f

    -- Elab args.
    (flip mapM_) (zip args argNames) $ \(t, n) -> do
        tacticN $ focus n
        elab t

    -- Cleanup. Very important.
    tacticN completeFill
    tacticN endUnify
    tacticN solve
    dropHoles
  where
    toFunc (PApp e' a') =
        let (f, args) = toFunc e'
        in (f, a' : args)
    toFunc e' = (e', [])
{-
elab (PApp e a) = do
    aHole <- getName "argTy"
    tacticN $ claim aHole (Type 0)

    bHole <- getName "retTy"
    tacticN $ claim bHole (Type 0)

    fHole <- getName "fElab"
    tacticN $ claim fHole $
        Bind "aXElab" (Pi $ Var Bound aHole (Type 0))
                 (Var Bound bHole (Type 0))

    sHole <- getName "sElab"
    tacticN $ claim sHole (Var Bound aHole (Type 0))

    -- XXX: ???
    tacticN $ prepFill fHole [sHole]

    tacticN $ focus fHole
    elab e

    tacticN $ focus sHole
    elab a

    -- XXX: ???
    tacticN completeFill
    tacticN endUnify
    tacticN solve
    dropHoles

    hs <- gets proofHoles
    when (aHole `elem` hs) $ tacticN (movelast aHole)
    when (bHole `elem` hs) $ tacticN (movelast bHole)
-}
elab PTypeI = do
    tacticN $ fill (Type 0)
    tacticN   solve
elab (PTypeE u) = do
    tacticN $ fill (Type u)
    tacticN   solve
elab (PBind _ Hole{} _) =
    lift . TypeError . Msg $
        "Hole in parsed PTerm. wtf?"
elab (PBind _ Guess{} _) =
    lift . TypeError . Msg $
        "Guess in parsed PTerm. wtf?"

checkPiGoal :: Name -> Elab ()
checkPiGoal n = do
    g <- binderTy <$> goal
    case g of
        Bind _ Pi{} _ -> return ()
        _ -> do
            a <- getName "pargTy"
            b <- getName "pretTy"
            f <- getName "pf"
            let fTy =
                    Bind n (Pi $ Var Bound a (Type 0)) $
                             Var Bound b (Type 0)
            tacticN $ claim a (Type 0)
            tacticN $ claim b (Type 0)
            tacticN $ claim f fTy
            tacticN $ movelast a
            tacticN $ movelast b
            tacticN $ fill (Var Bound f fTy)
            tacticN   solve
            tacticN $ focus f

goal :: Elab (Binder (Term Name))
goal = do
    hs <- gets proofHoles
    case hs of
        []      -> lift . TypeError . Msg $ "No holes for goal."
        (h : _) -> do
            pTy <- gets (ptTerm . proofTerm)
            findGoal h pTy
  where
    findGoal h (Bind n b@Guess{} e)
        | h == n    = return b
        | otherwise = findGoalB h b `mplus` findGoal h e
    findGoal h (Bind n b@Hole{} e)
        | h == n    = return b
        | otherwise = findGoalB h b `mplus` findGoal h e

    --- XXX: CORRECT?
    findGoal h (Bind _ b e) = findGoalB h b `mplus` findGoal h e

    findGoal h (App f a) = findGoal h f `mplus` findGoal h a
    findGoal h _ = do
        lift . TypeError . Msg $ "Can't find hole " ++ show h

    findGoalB h (Let t v)   = findGoal h t `mplus` findGoal h v
    findGoalB h (Guess t v) = findGoal h t `mplus` findGoal h v
    findGoalB h b           = findGoal h (binderTy b)

--- TESTING ----


traceState :: Elab ()
traceState =
    get >>= flip trace (return ()) . show . pPrint

myId :: TypeCheck Doc
myId = fmap pPrint . execStateT mkFun . newProof "myId" mempty $
    Constant (ConstTy IntTy)
{-    Bind "A" (Pi $ Type 0) .
    Bind "a" (Pi . Var Bound "A" $ Type 0) $
    Var Bound "a" (Var Bound "A" $ Type 0)-}

mkFun :: Elab ()
mkFun = do
{-
    aHole <- getName "argTy"
    tacticN $ claim aHole (Type 0)

    bHole <- getName "retTy"
    tacticN $ claim bHole (Type 0)

    fHole <- getName "fElab"
    tacticN $ claim fHole $
        Bind "aXElab" (Pi $ Var Bound aHole (Type 0))
                 (Var Bound bHole (Type 0))

    sHole <- getName "sElab"
    tacticN $ claim sHole (Var Bound aHole (Type 0))

    -- XXX: ???
    tacticN $ prepFill fHole [sHole]

    tacticN $ focus fHole
    mkId 

    tacticN $ focus sHole
    elab a

    -- XXX: ???
    tacticN completeFill
    tacticN endUnify
    tacticN solve
    dropHoles

    hs <- gets proofHoles
    when (aHole `elem` hs) $ tacticN (movelast aHole)
    when (bHole `elem` hs) $ tacticN (movelast bHole)
-}
    -- Create holes
    idF <- getName "idFunc"
    arg1 <- getName "A"
    arg2 <- getName "a"

    tacticN $ claim idF $
        Bind arg1 (Pi $ Type 0) .
        Bind arg2 (Pi . Var Bound arg1 $ Type 0) $
        Var Bound arg2 (Var Bound arg1 $ Type 0)
    tacticN $ claim arg1 $ Type 0
    tacticN $ claim arg2 $ Constant (ConstTy IntTy)

    tacticN $ prepFill idF [arg1, arg2]

    -- Create identity function
    tacticN $ focus idF
    mkId arg1 arg2

    -- Apply first arg
    tacticN $ focus arg1
    tacticN $ fill (Constant (ConstTy IntTy))
    tacticN   solve
    -- Apply second arg
    tacticN $ focus arg2
    tacticN $ fill (Constant (ConstInt 12))
    tacticN   solve

    -- XXX: ???
--    tacticN completeFill
    tacticN endUnify
    tacticN solve
    dropHoles


-- WHY NECESSARY
--    tacticN $ fill (Constant (ConstInt 12))
--    tacticN   solve

mkId :: Name -> Name -> Elab ()
mkId arg1 arg2 = do
    tacticN   attack
    tacticN $ intro (Just arg1)
    tacticN   attack
    tacticN $ intro (Just arg2)
    tacticN $ fill (Var Bound arg2 (Var Bound arg1 (Type 0)))
    forM_ [0..(2::Int)] . const $ tacticN solve
