{-# Language OverloadedStrings #-}
module Main where

import Utils
import Sizes

main :: IO ()
main =
  do prove_GFMUL
     -- prove_AES_128_ENC_x4
     -- prove_Polyval_Horner



prove_GFMUL :: IO ()
prove_GFMUL =
  doProof "_GFMUL" $

  do valH   <- fresh Vec "H"
     valRes <- fresh Vec "RES"


     let gpRegs _ = GPFresh AsBits
         vecRegs r =
            case r of
              YMM0 -> Just valRes
              YMM1 -> Just valH
              _    -> Nothing

     (r, basicPost) <- setupContext 1 gpRegs vecRegs

     let post = do basicPost

                   let ymm1 = valVecReg r YMM1
                   ymm1' <- getReg YMM1
                   expectSame "GFMUL preserves XMM1" ymm1 ymm1'

                   sawH   <- toSAW valH
                   sawRes <- toSAW valRes
                   ymm0   <- toSAW =<< getReg YMM0
                   ok     <- saw Bool =<<
                               cryTerm "GFMUL_post" [ sawH, sawRes, ymm0 ]
                   assert ok "Post condition not satisified."




     return (r,post)





prove_AES_128_ENC_x4 :: IO ()
prove_AES_128_ENC_x4 =
  doProof "AES_128_ENC_x4" $

  do (noncePtr,nonce) <- freshArray "IV" 16  Byte Immutable
     (ptPtr,pt)       <- freshArray "PT"  8  QWord Mutable
     (keyPtr,keys)    <- freshArray "Keys" (16 * 15) Byte Immutable

     let gpRegs r =
           case r of
             RDI -> gpUse noncePtr
             RSI -> gpUse ptPtr
             RDX -> gpUse keyPtr
             _   -> GPFresh AsBits

     (r,basicPost) <- setupContext 4 gpRegs (const Nothing)


     let post =
           do basicPost

              sIV <- packVec nonce
              sPT <- packVec pt
              sCT <- packVec =<< readArray QWord ptPtr 8
              sKs <- packVec keys
              ok <- saw Bool =<< cryTerm "post" [ sIV, sKs, sPT, sCT ]

              assert ok "Post condition not satisified."


     return (r,post)



prove_Polyval_Horner :: IO ()
prove_Polyval_Horner =
  doProof "Polyval_Horner" $

  do (ptrT,valT)      <- freshArray "T" 16 Byte Mutable
     (ptrH,valH)      <- freshArray "H" 16 Byte Immutable

     let blocks       = aad_size_blocks
         bufSize      = blocks * bytesToInteger block_size
     (ptrBuf,valBuf)  <- freshArray "buf" bufSize Byte Immutable
     valBlocks        <- literalAt QWord blocks

     see "T" ptrT
     see "H" ptrH
     see "Buf" ptrBuf

     let gpRegs r =
           case r of
             RDI -> gpUse ptrT
             RSI -> gpUse ptrH
             RDX -> gpUse ptrBuf
             RCX -> gpUse valBlocks
             _   -> GPFresh AsBits

     (r,basicPost) <- setupContext 14 gpRegs (const Nothing)

     return (r,basicPost)













