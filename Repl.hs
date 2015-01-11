module Repl where

import Control.Monad
import Control.Monad.Trans.Class
import Data.Monoid (mempty)

import System.Console.Haskeline

import Text.PrettyPrint.HughesPJClass

import Term
import Parser

replIO :: Context (PTerm Name) -> IO ()
replIO pctx = runInputT defaultSettings (repl pctx)

repl :: Context (PTerm Name) -> InputT IO ()
repl pctx = do
    mline <- getInputLine "> "
    when (mline /= Just ":q") $
        let line = maybe "" id mline
            parsed = iparse (allOf parseExpr) "stdin" line
        in case parsed of
            Left err -> lift (print err) >> repl pctx
            Right pterm ->
                case parsedCtxToCore [] pctx of
                    TypeError err ->
                        lift (putStrLn "Type Error in ctx" >> print err)
                    PassCheck ctx ->
                        processParsed ctx pterm
  where
    processParsed ctx pterm =
        case parsedToCore [] pctx pterm of
            TypeError err -> lift (print err) >> repl pctx
            PassCheck term -> do
                lift $ putStrLn "Parsed: "
                typeCheckFail (explicitHoles term ctx) $ \parsed -> do
                displayTerm ctx parsed

                let normalized = normalize parsed
                lift $ putStrLn "Normalized: "
                displayTerm ctx normalized

                let substd = substCtx normalized ctx
                lift $ putStrLn "Subst: "
                displayTerm ctx substd

                let substNorm = normalize substd
                lift $ putStrLn "Subst and Normalized: "
                displayTerm ctx substNorm

                repl pctx

    displayTerm ctx term =
        case typeOf [] ctx term of
            TypeError err -> lift (print err)
            PassCheck ty -> lift $ do
                print $ pPrint term
                putStr "    : "
                print $ pPrint ty

    typeCheckFail (PassCheck a) f = f a
    typeCheckFail (TypeError e) _ = lift (print e)


stdRepl = replIO stdlib

stdlib = parsef (allOf parseContext') "newParse" $
    "id (A : Type) (a : A) : A := a\n" ++
    "const (A : Type) (B : Type) (a : A) (b : B) : B := b\n" ++
    "aVal : Int := id _ (const _ _ 13.2 100)"
