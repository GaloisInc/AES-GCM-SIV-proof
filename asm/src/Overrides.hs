{-# Language DataKinds #-}
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

import SAWScript.X86(CallHandler,Sym)

import Lang.Crucible.LLVM.MemModel.Pointer
import Lang.Crucible.Simulator.RegValue
import Data.Macaw.X86.X86Reg
import Data.Macaw.X86.Symbolic



overrides :: Map (Natural,Integer) CallHandler
overrides = Map.fromList
  [ declare 0x400d50 gfmul_override
 ]

  where
  declare addr f = ( (4,addr), f )


gfmul_override :: CallHandler
gfmul_override (mem,r) =
   do let Just (RV s) = lookupX86Reg RSP r
          Just (RV i) = lookupX86Reg X86_IP r
      putStrLn $ "SP = " ++ show (ppPtr s) ++
                 ", IP = " ++ show (ppPtr i)
      putStrLn "RETURNING"
      return (mem,r) -- WRONG
 
