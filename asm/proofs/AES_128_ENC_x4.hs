{-# Language OverloadedStrings, RecordWildCards #-}
module Main where

import Utils
import Globals

main :: IO ()
main =
  doProof
    "verif-src/proof_target"
    "proofs/AES_128_ENC_x4.cry"
    "AES_128_ENC_x4" $

  do setupGlobals

     ipFun <- freshRegs
     let valIP = ipFun IP

     (noncePtr,nonce) <- freshArray "IV" 16  Byte Immutable
     (ptPtr,pt)       <- freshArray "PT"  8  QWord Mutable
     (keyPtr,keys)    <- freshArray "Keys" (16 * 15) Byte Immutable

{-
     debug ("\nArguments:")
     debug ("  Nonce = " ++ show (ppVal noncePtr))
     debug ("  CT    = " ++ show (ppVal ptPtr))
     debug ("  KEYS  = " ++ show (ppVal keyPtr))
-}

     (rsp,ret) <- setupStack
     valGPReg <- setupGPRegs $ \r ->
                    case r of
                      RSP -> gpUse rsp
                      RDI -> gpUse noncePtr
                      RSI -> gpUse ptPtr
                      RDX -> gpUse keyPtr
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

              sIV <- packVec nonce
              sPT <- packVec pt
              sCT <- packVec =<< readArray QWord ptPtr 8
              sKs <- packVec keys
              ok <- saw Bool =<< cryTerm "post" [ sIV, sKs, sPT, sCT ]

              assert ok "Post condition not satisified."


     return (r,post)




-- | Allocate the stack, and return the value for RSP, the return address.
setupStack :: Spec Pre (Value APtr, Value AQWord)
setupStack =
  -- Saves 3 registers: S1, S2, S3, RET
  do stack <- allocBytes "stack" Mutable (4 .* QWord)
     ret  <- fresh QWord "ret"
     p    <- ptrAdd stack (3 .* QWord)
     writeMem p ret

     return (p, ret)






