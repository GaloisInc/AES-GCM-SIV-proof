{-# Language OverloadedStrings, RecordWildCards #-}
module Main where

import Utils

main :: IO ()
main =
  doProof
    "verif-src/AES_128_ENC_x4"
    "proofs/AES_128_ENC_x4.cry"
    "AES_128_ENC_x4" $

  do setupGlobals

     ipFun <- freshRegs
     let valIP = ipFun IP

     (noncePtr,nonce) <- freshArray "IV" 16  Byte Immutable
     (ctPtr,ct)       <- freshArray "CT" 16 QWord Mutable
     (keyPtr,keys)    <- freshArray "Keys" (16 * 15) Byte Immutable

{-
     debug ("\nArguments:")
     debug ("  Nonce = " ++ show (ppVal noncePtr))
     debug ("  CT    = " ++ show (ppVal ctPtr))
     debug ("  KEYS  = " ++ show (ppVal keyPtr))
-}

     (rsp,ret) <- setupStack
     valGPReg <- setupGPRegs $ \r ->
                    case r of
                      RSP -> gpUse rsp
                      RDI -> gpUse noncePtr
                      RSI -> gpUse ctPtr
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

{-
              -- Arguments and results.
              let GPBits arg1 = valGPReg RDI
                  GPBits arg2 = valGPReg RSI
              res <- getReg (RAX,AsBits)
              a1 <- toSAW arg1
              a2 <- toSAW arg2
              re <- toSAW res

              ok <- saw Bool =<< cryTerm "post" [a1,a2,re]
              assert ok "Post condition not satisified."
-}

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


-- XXX: we should lookup address from the ELF file.
-- For the time being, we hard-code the locations
setupGlobals :: Spec Pre ()
setupGlobals =
  do let size = 0x400CFC
     reg <- allocBytes "globals" Immutable (size .* Byte)
     registerRegion 0 reg

     let declare _nm offset ty xs =
           do () <- return (const () (_nm :: String))
              ptr <- ptrAdd reg (offset .* Byte)
              writeMem ptr =<< mapM (literalAt ty) xs

     declare "con1"     0x4004c0 DWord [ 1, 1, 1, 1 ]
     declare "one"      0x4004f0 DWord [ 1, 0, 0, 0 ]
     declare "and_mask" 0x400500 DWord [ 0,0xffffffff, 0xffffffff, 0xffffffff ]





