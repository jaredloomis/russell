module Interpret where

import Control.Monad
import System.Console.Haskeline
import Control.Monad.State (evalStateT)

import Text.Parsec
import Text.Parsec.Pos (initialPos)

import Expr
import Parser
import Decl

interpret :: [PDecl (Expr Name)] -> IO ()
interpret ctx = do
    mline <- runInputT defaultSettings (getInputLine "> ")
    case mline of
        Just line -> when (line /= ":q") $
            case iparse (allOf parseExpr) "stdin" line of
                Right expr -> do
                    putStr "Raw Expr:\n"
                    displayExpr expr
                    putStr "Normalized Expr:\n"
                    displayExpr $ simplest expr
                    interpret ctx
                Left err   -> putStrLn $ "Parse Error: " ++ show err
        Nothing -> interpret ctx
  where
    simplest = normalize . substEnv (concatMap declNames ctx)

    displayExpr :: Expr Name -> IO ()
    displayExpr expr =
        case typeWith' ctx expr of
            Right ty -> do
                putStrLn $ showExpr expr
                putStrLn $ "     : " ++ showExpr ty
            Left err -> putStrLn $ "Type Error: " ++ err

--test :: IO ()
testI = case testDecl' of
    Right x -> interpret x
    Left err -> print err

testParse = iparse parseExpr "testParse" "Maybe Int"

--testTy = fmap whnf $ typeWith' testDecl' $
--    App (Par Ref (SName "Maybe")) (Const . ConstTy $ IntTy)

testDecl' = do
    id' <- iparse decl "id" $
        "id = \\(A : Type 0) => \\(a : A) => a"
    cons <- iparse decl "const" $
        "const = \\(A : Type 0) => \\(B : Type 0) => " ++
        "        \\(a : A) => \\(b : B) => b"
    mayb <- iparse decl "Maybe" $
        "data Maybe : Type 0 -> Type 0 where\n" ++
        "    Just : (a : Type 0) -> a -> Maybe a\n" ++
        "    Nothing : (a : Type 0) -> Maybe a"
    list <- iparse (allOf decl) "List" $
        "data List : Type 0 -> Type 0 where\n" ++
        "    Nil  : (a : Type 0) -> List a\n" ++
        "    Cons : (a : Type 0) -> a -> List a -> List a\n"
    return [id', cons, mayb, list]
