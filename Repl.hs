{-# LANGUAGE OverloadedStrings #-}
module Repl where

import Control.Monad
import Control.Monad.Trans.Class
import Control.Monad.State
import Control.Applicative

import System.Console.Haskeline

import Text.PrettyPrint.HughesPJClass

import Term
import Parser
import Tactic hiding (normalize)

replSettings :: Settings IO
replSettings =
    defaultSettings {
        historyFile = Just "/home/fiendfan1/.russel_history"
    }

replIO :: Context (PTerm Name) -> IO ()
replIO pctx = runInputT replSettings (repl pctx)

repl :: Context (PTerm Name) -> InputT IO ()
repl pctx = do
    mline <- getInputLine "Russel> "
    when (mline /= Just ":q") $
        let line = maybe "" id mline
            parsed = iparse (allOf parseExprAndType) "stdin" line
        in case parsed of
            Left err -> lift (print err) >> repl pctx
            Right (pterm, pty) ->
                case parsedCtxToCore [] pctx of
                    TypeError err ->
                        lift (putStrLn "Type Error in ctx" >> print err)
                    PassCheck ctx ->
--                        processParsed ctx pterm
                        processParsed' ctx pterm pty
  where
    processParsed' ctx pterm pty = do
        lift $ putStrLn "Parsed: "
        lift $ print pterm
        typeCheckFail (execStateT (elab pty) $
            newProof "type of repl term" ctx (Type 0)) $ \tyPs -> do
            let ty = ptTerm . proofTerm $ tyPs

            typeCheckFail (execStateT (elab pterm) $
                           newProof "repl term" ctx ty) $ \ps -> do
                lift . print . pPrint $ ps
                repl pctx

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

                let substd = substCtx ctx normalized
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
    typeCheckFail (TypeError e) _ = lift (print e) >> repl pctx

    parseExprAndType :: IParser (PTerm Name, PTerm Name)
    parseExprAndType =
        (,) <$> (lexeme parseExpr <* lexeme (reserved ":"))
            <*> lexeme parseExpr

stdRepl :: IO ()
stdRepl = replIO =<< stdlib

stdlib :: IO (Context (PTerm Name))
stdlib = do
    str <- readFile "Stdlib.rl"
    return $ parsef (allOf parseContext') "stdlib" str
