{-# Language RecordWildCards, DataKinds, FlexibleContexts, GADTs #-}
{-# Language TypeOperators #-}
module Utils (module Utils, module SAWScript.X86Spec) where

import GHC.TypeLits(type (<=), KnownNat)
import System.IO(hFlush,stdout)
import Data.ByteString(ByteString)
import Control.Exception(catch)
import System.Console.ANSI
import qualified Data.Map as Map

import Data.Parameterized.NatRepr(knownNat)

import SAWScript.X86
import SAWScript.X86Spec(Pre,Post,FunSpec(NewStyle))
import SAWScript.X86SpecNew hiding (cryConst, cryTerm)
import qualified SAWScript.X86SpecNew as New
import SAWScript.Prover.SolverStats
import SAWScript.Prover.Mode(ProverMode(Prove))

import Verifier.SAW.SharedTerm
import Verifier.SAW.FiniteValue(FirstOrderValue)
import Verifier.SAW.CryptolEnv(CryptolEnv)

import qualified Data.Macaw.X86.X86Reg as M

import System.Exit(exitFailure)

newProof ::
  ByteString {- ^ Name of the function -} ->
  Prover ->
  Specification ->
  IO Integer
newProof fun strategy pre =
  newProofIO fun strategy (\_ -> return pre)

newProofSizes ::
  ByteString {- ^ Name of the function -} ->
  Prover ->
  (Integer -> Integer -> Specification) ->
  IO Integer
newProofSizes fun strategy pre =
  newProofIO fun strategy $ \cry ->
    do let doGet x = case New.cryConst cry x of
                       Left err -> fail err
                       Right a  -> return a
       aad <- doGet "AAD_Size"
       msg <- doGet "MSG_Size"
       return (pre aad msg)


newProofIO ::
  ByteString {- ^ Name of the function -} ->
  Prover ->
  (CryptolEnv -> IO Specification) ->
  IO Integer
newProofIO fun strategy pre =
  do putStrLn (replicate 80 '-')
     let elf = "./verif-src/proof_target"
         cry = Just "cryptol/Asm128.cry"

         -- display _ = return () {-
         display  s = do debugPPReg M.RSP s
                         debugPPReg M.RDI s
                         debugPPReg M.RSI s
                         -- debugPPReg M.RDX s
                         -- debugPPReg M.RCX s
                         -- debugPPReg M.R8  s
          --}

     (ctx, addr, gs) <- proof linuxInfo elf cry (\_ _ -> return Map.empty)
                    Fun { funName = fun
                        , funSpec = NewStyle pre display }
     mapM_ (solveGoal strategy ctx) gs
     return addr
  `catch` \(X86Error e) -> do putStrLn e
                              say Red "  Proof failed"
                              exitFailure



type Prover = SharedContext ->
              ProverMode ->
              Term ->
              IO (Maybe [(String,FirstOrderValue)], SolverStats)

checkCryPost :: String -> [CryArg Post] -> (String, Prop Post)
checkCryPost p xs =
  checkPost ("Cryptol post-condition " ++ show p ++ " does not hold")
  (CryProp p xs)

checkPre :: a -> b -> (a,b)
checkPre = checkPost

checkPost :: a -> b -> (a,b)
checkPost x y = (x, y)

-- | Check that the value in a specific location contains a given value,
-- as defined by the Cryptol function.
checkCryPostDef ::
  (1 <= w, KnownNat w) =>
  V Post (LLVMPointerType w) -> String -> [CryArg Post] -> (String, Prop Post)
checkCryPostDef l f xs =
  checkPost (show l ++ " is not defined by " ++ show f)
            (l === CryFun knownNat f xs)

-- | Check that a specific pointer points to a memory location as
-- described by the given Cryptol funcion.
checkCryPointsTo ::
  V Post (LLVMPointerType 64) {- ^ This pointer pointrs to -} ->
  Integer                     {- ^ This many -} ->
  Unit                        {- ^ Values of this size -} ->
  String                      {- ^ As specified by this Cryptol function -} ->
  [CryArg Post]               {- ^ when applied to these arguments -} ->
  (String, Prop Post)
checkCryPointsTo l n u f xs =
  checkPost (show l ++ " is not defined by " ++ show f) (CryPostMem l n u f xs)



checkPreserves :: KnownType t => Loc t -> (String, Prop Post)
checkPreserves r =
  checkPost ("Location " ++ show r ++ " is not preserved.") (PreLoc r === Loc r)

stackAlloc :: Integer -> Alloc
stackAlloc locWords =
  InReg M.RSP := Area { areaName = "stack"
                      , areaMode = RW
                      , areaSize = (1 + locWords, QWords)
                      , areaHasPointers = False
                      , areaPtr  = locWords *. QWords
                      }

-- | Allocate a stack with some 64-bit argumetns
stackAllocArgs ::
  Integer {- ^ Number of QWord sized arguments -} ->
  Integer {- ^ Nubmer of QWords for local space -} ->
  (Integer -> Loc (LLVMPointerType 64), Alloc)
  -- ^ (Locations of arguments, and stack initialization)
stackAllocArgs argWords locWords =
  ( arg
  , InReg M.RSP := Area { areaName = "stack"
                        , areaMode = RW
                        , areaSize = (locWords + 1 + argWords,  QWords)
                        , areaHasPointers = False
                        , areaPtr  = locWords *. QWords
                        }
  )
  where
  arg i = inMem (InReg M.RSP) (1 + i) QWords



standardPost :: [ (String, Prop Post) ]
standardPost =
  [ checkPreserves (InReg M.RBX)
  , checkPreserves (InReg M.RBP)
  , checkPreserves (InReg M.R12)
  , checkPreserves (InReg M.R13)
  , checkPreserves (InReg M.R14)
  , checkPreserves (InReg M.R15)
  , preserveStack
  , preserveIP
  ]
  where

  preserveIP = checkPost "IP not restored"
             $ PreLoc (inMem (InReg M.RSP) 0 QWords) === Loc (InReg M.X86_IP)

  preserveStack = checkPost "Stack not restored"
                $ PreAddPtr (InReg M.RSP) 1 QWords === Loc (InReg M.RSP)


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

say :: Color -> String -> IO ()
say c x =
  do setSGR [SetConsoleIntensity BoldIntensity, SetColor Foreground Vivid c]
     putStr x
     setSGR [Reset]



ppReason :: Show a => Maybe a -> String
ppReason x =
  case x of
    Nothing -> "(unknown)"
    Just a  -> show a




