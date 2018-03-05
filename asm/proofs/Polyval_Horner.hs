{-# Language OverloadedStrings, RecordWildCards #-}
module Main where

import Utils
import Globals
import Sizes


main :: IO ()
main =
  doProof
    "verif-src/proof_target"
    "proofs/Polyval_Horner.cry"
    "Polyval_Horner" $

  do setupGlobals

     ipFun <- freshRegs
     let valIP = ipFun IP

     (ptrT,valT)      <- freshArray "T" 16 Byte Mutable
     (ptrH,valH)      <- freshArray "H" 16 Byte Immutable

     let blocks       = aad_size_blocks :: Integer
         bufSize :: Int
         bufSize      = fromIntegral (blocks * bytesToInteger block_size)
     (ptrBuf,valBuf)  <- freshArray "buf" bufSize Byte Immutable
     valBlocks        <- literalAt QWord blocks

     (rsp,ret) <- setupNoParamStack 14

     debug "\nParameters:"
     see "ptrT" ptrT
     see "ptrH" ptrH
     see "ptrBuf" ptrBuf
     see "stack" rsp



     valGPReg <- setupGPRegs $ \r ->
                    case r of
                      RSP -> gpUse rsp
                      RDI -> gpUse ptrT
                      RSI -> gpUse ptrH
                      RDX -> gpUse ptrBuf
                      RCX -> gpUse valBlocks
                      _   -> GPFresh AsBits


     valVecReg    <- freshRegs
     valFPReg     <- freshRegs
     valFlag      <- freshRegs
     valX87Status <- freshRegs
     valX87TopF   <- freshRegs
     let valX87Top = valX87TopF X87Top
     valX87Tag <- freshRegs
     let r = RegAssign { .. }

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

     return (r,post)









