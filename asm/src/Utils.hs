{-# Language RecordWildCards #-}
module Utils (module Utils, module SAWScript.X86Spec) where

import System.IO(hFlush,stdout)
import Data.ByteString(ByteString)
import Control.Exception(catch)
import Control.Concurrent(forkIO,newEmptyMVar,takeMVar,putMVar,killThread)

import SAWScript.X86
import SAWScript.X86Spec
import SAWScript.Prover.SolverStats
import SAWScript.Prover.Mode(ProverMode(Prove))

import Verifier.SAW.SharedTerm
import Verifier.SAW.FiniteValue(FirstOrderValue)
import Data.Parameterized.NatRepr(natValue)

import Globals(setupGlobals)
import Overrides(setupOverrides)


see :: Infer t => String -> Value t -> Spec p ()
see x v = debug (x ++ " =" ++ ppVal v)

type Prover = SharedContext ->
              ProverMode ->
              Term ->
              IO (Maybe [(String,FirstOrderValue)], SolverStats)

doProof ::
  ByteString {- ^ Name of the function -} ->
  Prover ->
  Spec Pre (RegAssign, Spec Post ()) {- ^ Spec for the function -} ->
  IO ()
doProof fun strategy pre =
  do putStrLn (replicate 80 '-')
     let cry = "../cryptol-specs/Asm128.cry"
     (ctx, gs) <- proof linuxInfo "./verif-src/proof_target"
                                  (setupOverrides cry)
            Fun { funName = fun
                , funSpec = FunSpec
                    { spec     = pre
                    , cryDecls = Just cry
                    } }
     mapM_ (solveGoal strategy ctx) gs
  `catch` \(X86Error e) -> putStrLn e


-- | Basic pre-condition setup.
-- Intiializes complex machine instructions, globals,
-- the stack, and X87 state.
setupContext ::
  Integer {- ^ Size of stack in QWords -} ->
  (GPReg -> GPSetup) {- ^ Initialization for GP regs (stack auto) -} ->
  (VecReg -> Maybe (Value AVec)) {- ^ Setup for vector registers -} ->
  Spec Pre (RegAssign, Spec Post ())
setupContext stackSize setupGP setupVec =
  do setupComplexInstructions
     setupGlobals

     ipFun <- freshRegs
     let valIP = ipFun IP

     (rsp,ret) <- setupNoParamStack stackSize

     see "RSP" rsp

     valGPReg <- setupGPRegs $ \r ->
                   case r of
                     RSP -> gpUse rsp
                     _   -> setupGP r

     valVecReg <- setupVecRegs setupVec

     -- X87, unused in these proofs
     valFPReg     <- freshRegs
     valFlag      <- freshRegs
     valX87Status <- freshRegs
     valX87TopF   <- freshRegs
     let valX87Top = valX87TopF X87Top
     valX87Tag <- freshRegs
     let r = RegAssign { .. }

     -- basic post
     let post =
            do preserveGP r RBX
               preserveGP r RBP
               preserveGP r R12
               preserveGP r R13
               preserveGP r R14
               preserveGP r R15

               expectRSP <- ptrAdd rsp (1 .* QWord)
               expectSame "RSP" expectRSP =<< getReg (RSP,AsPtr)

               expectSame "IP" ret =<< getReg IP

     return (r, post)



setupComplexInstructions :: Spec Pre ()
setupComplexInstructions =
  do aesenc     <- cryTerm "aesenc" []
     aesenclast <- cryTerm "aesenclast" []
     clmul      <- cryTerm "clmul" []
     let bin f = \sc x y -> scApplyAll sc f [x,y]

     registerSymFuns SymFunTerms
                       { termAesEnc = bin aesenc
                       , termAesEncLast = bin aesenclast
                       , termClMul = bin clmul
                       }

solveGoal :: Prover -> SharedContext -> Goal -> IO ()
solveGoal prover ctx g =
  do term <- gGoal ctx g
     putStrLn "Proving goal"
     putStrLn ("  Source: " ++ show (gLoc g))
     putStrLn ("  Reason: " ++ ppReason (gMessage g))
     putStr "  Working... "
     hFlush stdout
     writeFile "GG.hs" (scPrettyTerm defaultPPOpts term)
     (mb, stats) <- prover ctx Prove term
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


-- | If each term is of type @[n]@, then the result is of type @[x][n]@
wordVec :: SharedContext -> Integer -> [Term] -> IO Term
wordVec sc n xs =
  do t <- scBitvector sc (fromInteger n)
     scVector sc t xs


packVecAt :: SAW t => X86 t -> [Value t] -> Spec p Term
packVecAt ty xs =
  do ys <- mapM toSAW xs
     withSharedContext $ \sc -> wordVec sc (natValue (bitSize ty)) ys

packVec :: (Infer t, SAW t) => [Value t] -> Spec p Term
packVec = packVecAt infer




-- | Allocate a blank stack, assuming no parameters will be passed on the
-- stack. Returns the value for RSP, the return address.
setupNoParamStack :: Integer -> Spec Pre (Value APtr, Value AQWord)
setupNoParamStack size =
  do stack <- allocBytes "stack" Mutable (size .* QWord)
     ret  <- fresh QWord "ret"
     p    <- ptrAdd stack ((size - 1) .* QWord)
     writeMem p ret

     return (p, ret)


assertPost :: ByteString -> String -> [Term] -> Spec Post ()
assertPost fun cryName args =
  do ok <- saw Bool =<< cryTerm cryName args
     assert ok ("Post condition for " ++ show fun)

oneOf :: [ Prover ] -> Prover
oneOf ps sc mode term =
  do res <- newEmptyMVar
     workers <- mapM (startWorker res) ps
     r <- takeMVar res
     mapM_ killThread workers
     return r
  where
  startWorker res p = forkIO (putMVar res =<< p sc mode term)




