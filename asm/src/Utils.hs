{-# Language RecordWildCards, DataKinds #-}
module Utils (module Utils, module SAWScript.X86Spec) where

import System.IO(hFlush,stdout)
import Data.ByteString(ByteString)
import Control.Exception(catch)
import Control.Concurrent(forkIO,newEmptyMVar,takeMVar,putMVar,killThread)
import System.Console.ANSI


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
     let elf = "./verif-src/proof_target"
         cry = Just "cryptol/Asm128.cry"

     (ctx, gs) <- proof linuxInfo elf cry setupOverrides
                    Fun { funName = fun, funSpec = OldStyle pre }
     mapM_ (solveGoal strategy ctx) gs
  `catch` \(X86Error e) -> putStrLn e


-- | Basic pre-condition setup.
-- Intiializes complex machine instructions, globals,
-- the stack, and X87 state.
setupContext ::
  Integer {- ^ Number of QWords for parameters -} ->
  Integer {- ^ Number of QWords for locals -} ->
  (GPReg -> GPSetup) {- ^ Initialization for GP regs (stack auto) -} ->
  (VecReg -> Maybe (Value (Bits 256))) {- ^ Setup for vector registers -} ->
  Spec Pre (Value APtr, RegAssign, Spec Post ())
  -- ^ Pointer to the last (smallest) parameter, reg assign, and post cond
setupContext pNum lNum setupGP setupVec =
  do setupComplexInstructions
     setupGlobals

     ipFun <- freshRegs
     let valIP = ipFun IP

     (locals,rsp,ret) <- setupStack pNum lNum

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

     return (locals, r, post)



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
     putStrLn ("  Source:   " ++ show (gLoc g))
     putStrLn ("  Avoiding: " ++ ppReason (gMessage g))
     putStr "  Working... "
     hFlush stdout
     writeFile "GG.hs" (scPrettyTerm defaultPPOpts term)
     (mb, stats) <- prover ctx Prove term
     putStrLn (ppStats stats)
     case mb of
       Nothing -> say Green "  Success!\n"
       Just a  -> do say Red "  Proof failed"
                     putStrLn ", counter-example:"
                     let pp (x,y) = putStrLn ("    " ++ x ++ " = " ++ show y)
                     mapM_ pp a
  where
  say c x =
    do setSGR [SetConsoleIntensity BoldIntensity, SetColor Foreground Vivid c]
       putStr x
       setSGR [Reset]



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





setupStack ::
  Integer {- ^ Number of QWords for parameters -} ->
  Integer {- ^ Number of local QWords (not counting return addr) -} ->
  Spec Pre (Value APtr, Value APtr, Value (Bits 64))
  -- ^ (pointer to last parameter--least one, value for RSP, return address)
setupStack paramNum localNum =
  do let size = paramNum + 1 + localNum
     stack <- allocBytes "stack" Mutable (size .* QWord)
     ret  <- fresh QWord "ret"
     l    <- ptrAdd stack ((size - 1 - paramNum) .* QWord)
     writeMem l ret

     p    <- ptrAdd l (1 .* QWord) -- ptr to the last parameter

     return (p, l, ret)


assertPost :: ByteString -> String -> [Term] -> Spec Post ()
assertPost fun cryName args =
  do ok <- saw Bool =<< cryTerm cryName args
     assert ok ("Failure of post condition for " ++ show fun)

oneOf :: [ Prover ] -> Prover
oneOf ps sc mode term =
  do res <- newEmptyMVar
     workers <- mapM (startWorker res) ps
     r <- takeMVar res
     mapM_ killThread workers
     return r
  where
  startWorker res p = forkIO (putMVar res =<< p sc mode term)




