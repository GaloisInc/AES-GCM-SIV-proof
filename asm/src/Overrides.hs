{-# Language DataKinds, ImplicitParams #-}
{-^ This module contains the specifiecations for the functions
that are used when they are called from other functions.

IMPORTANT: This should match what we proved!

XXX: These should be computed from the specification we proved,
but we are not there yet.

XXX: The function locations should be specified in some more robust way.
-}
module Overrides where

import GHC.Natural
import Data.Map(Map)
import qualified Data.Map as Map

import Data.Parameterized.Context (Assignment)


import Lang.Crucible.Types
import Lang.Crucible.Simulator.RegValue
import Lang.Crucible.Solver.Interface
import Lang.Crucible.Solver.Symbol(userSymbol)
import Lang.Crucible.Solver.SAWCoreBackend
                  (toSC, sawBackendSharedContext, bindSAWTerm)
import Lang.Crucible.LLVM.MemModel(doPtrAddOffset)
import Lang.Crucible.LLVM.MemModel.Pointer
import Data.Macaw.X86.X86Reg
import Data.Macaw.X86.Symbolic
import Data.Macaw.X86.ArchTypes(X86_64)
import Data.Macaw.Symbolic.PersistentState
import Data.Macaw.Symbolic.CrucGen
import Verifier.SAW.SharedTerm

import Verifier.SAW.CryptolEnv(CryptolEnv(eTermEnv))

import SAWScript.X86(CallHandler,Sym)
import SAWScript.X86Spec.Monad(lookupCry)

-- XXX: The addressing story here is extermely ad-hoc.
setupOverrides :: Sym -> CryptolEnv -> IO (Map (Natural,Integer) CallHandler)
setupOverrides _sym cenv =
  do sawDot <- lookupCry "dot256" (eTermEnv cenv)
     -- why are these in different pointer regions?
     return $ Map.fromList
       [ declare (4,0x400d50) (gfmul_override sawDot)
       , declare (6,0x400d50) (gfmul_override sawDot)
       ]

  where
  declare addr f = ( addr, f )

n256 :: NatRepr 256
n256 = knownNat

gfmul_override :: Term -> CallHandler
gfmul_override dot sym (mem,r) =
  do putStr ("\n*** Enter GFMUL override... ")
     ymm2 <- freshYMM sym 2
     ymm3 <- freshYMM sym 3
     ymm4 <- freshYMM sym 4
     ymm5 <- freshYMM sym 5

     let Just (RV sp)   = lookupX86Reg RSP r
         Just (RV res0) = lookupX86Reg (YMM 0) r
         Just (RV h)    = lookupX86Reg (YMM 1) r
{-
     print ("SP on entry = " ++ show (ppPtr sp))

     putStrLn "MEMORY:"
     print (ppMem mem)
-}
     let ?ptrWidth = knownNat
{-
     ip <- do x <- doLoad sym mem sp (bitvectorType 8) 0
              v <- coerceAny sym (LLVMPointerRepr knownNat) x
              return (RV v)
-}
     newSP <- RV <$> (doPtrAddOffset sym mem sp =<< bvLit sym knownNat 8)


     sawRes0 <- toSC sym =<< projectLLVM_bv sym res0
     sawH    <- toSC sym =<< projectLLVM_bv sym h


     ctx <- sawBackendSharedContext sym
     sawRes <- scApplyAll ctx dot [ sawRes0, sawH ]
     res <- llvmPointer_bv sym =<< bindSAWTerm sym (BaseBVRepr n256) sawRes

     let r1 = {-updReg X86_IP ip
            $ -}updReg RSP newSP
            $ updReg (YMM 0) (RV res)
            $ updReg (YMM 2) ymm2
            $ updReg (YMM 3) ymm3
            $ updReg (YMM 4) ymm4
            $ updReg (YMM 5) ymm5
              r


     putStrLn "Exit"
     return (mem,r1)


updReg :: X86Reg t ->
          f (ToCrucibleType t) ->
          Assignment f (MacawCrucibleRegTypes X86_64) ->
          Assignment f (MacawCrucibleRegTypes X86_64)
updReg r x a = case updateX86Reg r (const x) a of
                 Just a1 -> a1
                 Nothing -> error ("[bug] Unknown register: " ++ show r)


freshYMM :: Sym -> Int -> IO (RegValue' Sym (LLVMPointerType 256))
freshYMM sym n =
  do base_nm <- symName ("YMM" ++ show n ++ "_base")
     off_nm  <- symName ("YMM" ++ show n ++ "_offset")
     base    <- freshConstant sym base_nm BaseNatRepr
     offs    <- freshConstant sym off_nm (BaseBVRepr knownNat)
     return (RV (LLVMPointer base offs))

symName :: String -> IO SolverSymbol
symName s = case userSymbol s of
              Left err -> fail (show err)
              Right a  -> return a

