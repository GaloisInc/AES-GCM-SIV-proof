module Utils (module Utils, module SAWScript.X86Spec) where

import System.IO(hFlush,stdout)
import Data.ByteString(ByteString)
import Control.Exception(catch)

import SAWScript.X86
import SAWScript.X86Spec

import SAWScript.Prover.Mode(ProverMode(Prove))
import SAWScript.Prover.SBV(satUnintSBV,z3)
import SAWScript.Prover.SolverStats

doProof ::
  FilePath {- ^ Binary file -} ->
  FilePath {- ^ Cryptol spe file -} ->
  ByteString {- ^ Name of the function -} ->
  Spec Pre (RegAssign, Spec Post ()) {- ^ Spec for the function -} ->
  IO ()
doProof file cry fun pre =
  do (ctx, gs) <- proof linuxInfo file
            Fun { funName = fun
                , funSpec = FunSpec
                    { spec     = pre
                    , cryDecls = Just cry
                    } }
     mapM_ (solveGoal ctx) gs
  `catch` \(X86Error e) -> putStrLn e



solveGoal :: SharedContext -> Goal -> IO ()
solveGoal ctx g =
  do term <- gGoal ctx g
     putStrLn "Proving goal"
     putStrLn ("  Source: " ++ show (gLoc g))
     putStrLn ("  Reason: " ++ ppReason (gMessage g))
     putStr "  Working... "
     hFlush stdout
     (mb, stats) <- satUnintSBV z3 ctx [] Prove term
     putStrLn (ppStats stats)
     case mb of
       Nothing -> putStrLn "  Success!"
       Just a  -> do putStrLn "  Proof failed, counter-example:"
                     let pp (x,y) = putStrLn ("    " ++ x ++ " = " ++ show y)
                     mapM_ pp a

ppReason :: Show a => Maybe a -> String
ppReason x =
  case x of
    Nothing -> "(unknown)"
    Just a  -> show a


ppGG :: Goal -> IO ()
ppGG g =
  do putStrLn "-------------"
     putStrLn "Assuming:"
     mapM_ (putStrLn . showTerm) (gAssumes g)
     putStrLn "Shows:"
     putStrLn (showTerm (gShows g))
     putStrLn "---------------"


