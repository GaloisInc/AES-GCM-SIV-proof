{-# Language OverloadedStrings #-}
module Main where

import Data.ByteString(ByteString)
import Control.Monad(forM_)

import SAWScript.Prover.SBV(satUnintSBV,z3,cvc4,yices)
import SAWScript.Prover.RME(satRME)
import SAWScript.Prover.ABC(satABC)
import SAWScript.Prover.Exporter

import SAWScript.X86Spec.Memory


import Utils
import Sizes

main :: IO ()
main =
  do -- prove_GFMUL "_GFMUL"
     -- prove_GFMUL "GFMUL"
     -- prove_Polyval_Horner
     -- prove_Polyval_Horner_AAD_MSG_LENBLK
     -- prove_AES_128_ENC_x4
     -- prove_AES_KS_ENC_x1
     -- prove_ENC_MSG_x4
     prove_ENC_MSG_x8

     -- prove_test

prove_test :: IO ()
prove_test =
  doProof "galois_xxx" strategy $
  do xmm0 <- saw V256 =<< cryTerm "test_xmm0" []
     xmm1 <- saw V256 =<< cryTerm "test_xmm1" []
     let vecRegs r = case r of
                       YMM0 -> Just xmm0
                       YMM1 -> Just xmm1
                       _    -> Nothing
     (_,r,_basicPost) <- setupContext 0 0 (const (GPFresh AsBits)) vecRegs
     let post =
          do v <- toSAW =<< getReg YMM2
             assertPost "galois_xxx" "test_post" [v]

     return (r,post)

  where
  strategy = satUnintSBV z3 []


prove_GFMUL :: ByteString -> IO ()
prove_GFMUL gfMulVer =
  doProof gfMulVer strategy $
  do valH   <- fresh V256 "H"
     valRes <- fresh V256 "RES"

     let gpRegs _ = GPFresh AsBits
         vecRegs r =
            case r of
              YMM0 -> Just valRes
              YMM1 -> Just valH
              _    -> Nothing

     (_, r, basicPost) <- setupContext 0 0 gpRegs vecRegs

     let post = do basicPost

                   let ymm1 = valVecReg r YMM1
                   ymm1' <- getReg YMM1
                   expectSame "GFMUL preserves XMM1" ymm1 ymm1'

                   sawH   <- toSAW valH
                   sawRes <- toSAW valRes
                   ymm0   <- toSAW =<< getReg YMM0
                   assertPost gfMulVer "GFMUL_post" [ sawH, sawRes, ymm0 ]

     return (r,post)

  where
  strategy = satRME




prove_AES_128_ENC_x4 :: IO ()
prove_AES_128_ENC_x4 =
  let name = "AES_128_ENC_x4" in
  doProof name strategy $
  do
     -- The nonce is 12 bytes, padded to 16 
     (noncePtr,nonce) <- freshArray "IV" 16  Byte Immutable
     forM_ (drop 12 nonce) $ \v -> assume =<< sameVal v =<< literal 0

     ctPtr          <- allocBytes "CT" Mutable (4 .* V128)
     (keyPtr,keys)  <- freshArray "Keys" (11 * 16) Byte Immutable

     let gpRegs r =
           case r of
             RDI -> gpUse noncePtr
             RSI -> gpUse ctPtr
             RDX -> gpUse keyPtr
             _   -> GPFresh AsBits

     (_,r,basicPost) <- setupContext 0 3 gpRegs (const Nothing)


     let post =
           do basicPost

              sIV <- packVec nonce
              sCT <- packVec =<< readArray V128 ctPtr 4
              sKs <- packVec keys
              assertPost name "AES_128_ENC_x4_post" [ sIV, sKs, sCT ]


     return (r,post)
  where strategy = satUnintSBV z3 [ "aes_round", "aes_final_round" ]

prove_Polyval_Horner :: IO ()
prove_Polyval_Horner =
  let name = "Polyval_Horner" in
  doProof name strategy $
  do (ptrT,valT)      <- freshArray "T" 16 Byte Mutable
     (ptrH,valH)      <- freshArray "H" 16 Byte Immutable

     let aadSize      = bytesToInteger aad_size
     (ptrBuf,valBuf)  <- freshArray "buf" aadSize Byte Immutable
     valSize          <- literalAt QWord aadSize

     see "T" ptrT
     see "H" ptrH
     see "Buf" ptrBuf

     let gpRegs r =
           case r of
             RDI -> gpUse ptrT
             RSI -> gpUse ptrH
             RDX -> gpUse ptrBuf
             RCX -> gpUse valSize
             _   -> GPFresh AsBits

     -- Save 10 registers; 16 bytes local (2 qwords); RET for call
     (_,r,basicPost) <- setupContext 0 (10 + 2 + 1) gpRegs (const Nothing)

     let post =
          do basicPost
             sH  <- packVec valH
             sI  <- packVec valBuf
             sT  <- packVec valT
             sT' <- packVec =<< readArray Byte ptrT 16
             assertPost name "Polyval_Horner_post" [ sH, sI, sT, sT' ]

     return (r,post)

  where strategy = satUnintSBV yices ["dot"]


prove_Polyval_Horner_AAD_MSG_LENBLK :: IO ()
prove_Polyval_Horner_AAD_MSG_LENBLK =
  let name = "Polyval_Horner_AAD_MSG_LENBLK" in
  doProof name strategy $
  do (ptrT, valT)    <- freshArray "T" 16 Byte Mutable
     (ptrH, valH)    <- freshArray "H" 16 Byte Immutable

     let aadSize      = bytesToInteger aad_size
     (ptrAAD,valAAD) <- freshArray "AAD" aadSize Byte Immutable
     valAADLen       <- literalAt QWord aadSize

     let msgSize      = bytesToInteger msg_size
     (ptrPT, valPT)  <- freshArray "PT" msgSize Byte Immutable
     valMsgLen       <- literalAt QWord msgSize

     (ptrLenBlk, valLenBlk) <- freshArray "LEN_BLK" 2 QWord Immutable

     let gpRegs r =
           case r of
             RDI -> gpUse ptrT
             RSI -> gpUse ptrH
             RDX -> gpUse ptrAAD
             RCX -> gpUse valAADLen
             R8  -> gpUse ptrPT
             R9  -> gpUse valMsgLen
             _   -> GPFresh AsBits

     -- Save 12 registers, 16 bytes local (2 qwords); ret for call
     (paramPtr, r, basicPost) <- setupContext 1 (12 + 2 + 1)
                                              gpRegs (const Nothing)

     writeMem paramPtr ptrLenBlk

     let post =
           do basicPost
              sH      <- packVec valH
              sAAD    <- packVec valAAD
              sPT     <- packVec valPT
              sLenBlk <- packVec valLenBlk
              sT      <- packVec valT
              sT'     <- packVec =<< readArray Byte ptrT 16

              assertPost name "Polyval_Horner_AAD_MSG_post"
                 [ sH, sAAD, sPT, sLenBlk, sT, sT' ]

     return (r, post)

  where strategy = satUnintSBV yices ["dot"]


prove_AES_KS_ENC_x1 :: IO ()
prove_AES_KS_ENC_x1 =
  let name = "AES_KS_ENC_x1" in
  doProof name strategy $
  do (ptrPT, valPT)     <- freshArray "PT" 16 Byte Immutable
     ptrCT              <- allocBytes "CT" Mutable (16 .* Byte)
     ptrKeys            <- allocBytes "Keys" Mutable (11 .* V128)

     (ptrIKey,valIKey)  <- freshArray "IKey" 16 Byte Immutable

     let gpRegs r =
           case r of
             RDI -> gpUse ptrPT
             RSI -> gpUse ptrCT
             -- RDX: unused parameter
             RCX -> gpUse ptrKeys
             R8  -> gpUse ptrIKey
             _   -> GPFresh AsBits

     -- Save 6 registers
     (_, r, basicPost) <- setupContext 0 6 gpRegs (const Nothing)

     let post =
          do basicPost
             sIKey  <- packVec valIKey
             sPT    <- packVec valPT
             sCT    <- packVec =<< readArray Byte ptrCT 16
             sKeys  <- packVec =<< readArray Byte ptrKeys (11 * 16)
             assertPost name "AES_KS_ENC_x1_post1" [ sIKey, sKeys ]
             assertPost name "AES_KS_ENC_x1_post2" [ sKeys, sPT, sCT ]

     return (r,post)

  where strategy = satABC


prove_ENC_MSG_x4 :: IO ()
prove_ENC_MSG_x4 =
  let name = "ENC_MSG_x4" in
  doProof name strategy $
  do let msgSize = bytesToInteger msg_size
     (ptrPT, valPT)     <- freshArray "PT" msgSize Byte Immutable
     valMsgLen          <- literalAt QWord msgSize

     ptrCT              <- allocBytes "CT" Mutable (msgSize .* Byte)
     (ptrTAG, valTag)   <- freshArray "TAG" 16 Byte Immutable
     (ptrKeys, valKeys) <- freshArray "Keys" (11 * 16) Byte Immutable

     see "TAG" ptrTAG
     see "KEYS" ptrKeys

     let gpRegs r = case r of
                      RDI -> gpUse ptrPT
                      RSI -> gpUse ptrCT
                      RDX -> gpUse ptrTAG
                      RCX -> gpUse ptrKeys
                      R8  -> gpUse valMsgLen
                      _   -> GPFresh AsBits

     -- Save 10 register; 16 bytes (2 qwords) of local space.
     (_, r, basicPost) <- setupContext 0 (10 + 2) gpRegs (const Nothing)

     let post =
          do basicPost
             sPT   <- packVec valPT
             sCT   <- packVec =<< readArray Byte ptrCT msgSize
             sTAG  <- packVec valTag
             sKeys <- packVec valKeys
             assertPost name "ENC_MSG_post" [ sKeys, sTAG, sPT, sCT ]

     return (r,post)
  where
  strategy = satUnintSBV z3 [ "aes_round", "aes_final_round" ]


prove_ENC_MSG_x8 :: IO ()
prove_ENC_MSG_x8 =
  let name = "ENC_MSG_x8" in
  doProof name strategy $
  do let msgSize = bytesToInteger msg_size
     (ptrPT, valPT)     <- freshArray "PT" msgSize Byte Immutable
     valMsgLen          <- literalAt QWord msgSize

     ptrCT              <- allocBytes "CT" Mutable (msgSize .* Byte)
     (ptrTAG, valTag)   <- freshArray "TAG" 16 Byte Immutable
     (ptrKeys, valKeys) <- freshArray "Keys" (11 * 16) Byte Immutable

     see "TAG" ptrTAG
     see "KEYS" ptrKeys

     let gpRegs r = case r of
                      RDI -> gpUse ptrPT
                      RSI -> gpUse ptrCT
                      RDX -> gpUse ptrTAG
                      RCX -> gpUse ptrKeys
                      R8  -> gpUse valMsgLen
                      _   -> GPFresh AsBits

     -- Save 12 register;
     -- 128 bytes (16 qwords) of local space;
     -- 63 bytes for alignment (~ 8 words)
     -- 16 bytes (2 qwords)
     (_, r, basicPost) <- setupContext 0 (12 + 16 + 8 + 2)
                                                  gpRegs (const Nothing)

     let post =
          do basicPost
             sPT   <- packVec valPT
             sCT   <- packVec =<< readArray Byte ptrCT msgSize
             sTAG  <- packVec valTag
             sKeys <- packVec valKeys
             assertPost name "ENC_MSG_post" [ sKeys, sTAG, sPT, sCT ]

     return (r,post)
  where
  strategy = satUnintSBV z3 [ "aes_round", "aes_final_round" ]


