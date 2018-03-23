{-# Language OverloadedStrings, DataKinds, TypeOperators #-}
module Main where

import GHC.TypeLits(type (*))

import Data.ByteString(ByteString)

import SAWScript.Prover.SBV(satUnintSBV,z3,cvc4,yices)
import SAWScript.Prover.RME(satRME)
import SAWScript.Prover.ABC(satABC)
import SAWScript.Prover.Exporter

import SAWScript.X86Spec.Memory

import SAWScript.X86SpecNew hiding (cryConst, cryTerm)
import qualified Data.Macaw.X86.X86Reg as M


import Utils
import Globals





main :: IO ()
main =
  do -- prove_GFMUL "_GFMUL"
     -- prove_GFMUL "GFMUL"
     -- prove_Polyval_Horner
     -- prove_Polyval_Horner_AAD_MSG_LENBLK
     --prove_INIT_Htable
     -- prove_Polyval_Htable
     -- prove_AES_128_ENC_x4
     -- prove_AES_KS_ENC_x1
     prove_ENC_MSG_x4
     -- prove_ENC_MSG_x8





prove_INIT_Htable :: IO()
prove_INIT_Htable =
  let name = "INIT_Htable" in
  doProof name strategy $
  do
    (htblPtr,htbl) <- freshArray "Htbl" (16*8) Byte Mutable
    (hPtr,h) <- freshArray "H" 16  Byte Immutable

    let gpRegs r = case r of
                    RDI -> gpUse htblPtr
                    RSI -> gpUse hPtr
                    _   -> GPFresh AsBits

    (_, r, basicPost) <- setupContext 0 0 gpRegs (const Nothing)

    let post =
          do  basicPost
              sawRes <- packVec =<< readArray Byte htblPtr 128
              sawH <- packVec h
              assertPost name "INIT_Htable_post" [ sawH, sawRes ]

    return (r, post)
  where
  strategy = satUnintSBV z3 ["dot"]


prove_Polyval_Htable :: IO()
prove_Polyval_Htable =
  let name = "Polyval_Htable" in
  doProof name strategy $
  do
    (ptrHtable,htable) <- freshArray "Htbl" (16*8) Byte Mutable
    see "Htable" ptrHtable
    (ptrT,valT)      <- freshArray "T" 16 Byte Mutable
    see "T" ptrT
    aadSize          <- cryConst "AAD_Size"
    (ptrBuf,valBuf)  <- freshArray "buf" aadSize Byte Immutable
    see "Buf" ptrBuf
    valSize          <- literalAt QWord aadSize

    let gpRegs r =
          case r of
            RDI -> gpUse ptrHtable
            RSI -> gpUse ptrBuf
            RDX -> gpUse valSize
            RCX -> gpUse ptrT
            _   -> GPFresh AsBits

-- Save 12 registers; 16 bytes local (2 qwords); RET for call
    (_,r,basicPost) <- setupContext 0 (12 + 2) gpRegs (const Nothing)

    let post =
          do  basicPost
              sI  <- packVec valBuf
              sT' <- packVec =<< readArray Byte ptrT 16
              sTbl <- packVec htable
              assertPost name "Polyval_HTable_post" [ sI, sTbl, sT' ]

    return (r,post)
  where
    strategy = satUnintSBV z3 []


prove_GFMUL :: ByteString -> IO ()
prove_GFMUL gfMulVer =
  newProof gfMulVer strategy
    Specification
      { specAllocs  = [ stackAlloc 0 ]
      , specPres    = []
      , specPosts   =
          standardPost ++
          [ checkPreserves h
          , checkCryPostDef res "dot256" [ cryPre h, cryPre res ]
          ]
      , specGlobsRO = globals
      }
  where
  res = InReg (M.YMM 0)
  h   = InReg (M.YMM 1)

  strategy = satRME



prove_Polyval_Horner :: IO ()
prove_Polyval_Horner =
  newProofSizes "Polyval_Horner" strategy $ \aadSize _msgSize ->
  Specification
    { specAllocs =
      [ -- Save 10 registers; 16 bytes local (2 qwords); RET for call
        stackAlloc (10 + 2 + 1)

      , vT   := area "T"   RW 16      Bytes
      , vH   := area "H"   RO 16      Bytes
      , vBuf := area "buf" RO aadSize Bytes
      ]

    , specPres = [ checkPre "Invalid AAD Size" (Loc vSize === intLit aadSize) ]

    , specPosts = standardPost ++
        [ checkCryPostDef resLoc
             "Polyval_Horner_def"
                [ cryArrPre vH   16      Bytes
                , cryArrPre vBuf aadSize Bytes
                , cryArrPre vT   16      Bytes
                ]
       ]

    , specGlobsRO = globals
    }
  where
  vT    = InReg M.RDI
  vH    = InReg M.RSI
  vBuf  = InReg M.RDX
  vSize = InReg M.RCX

  resLoc :: Loc (LLVMPointerType 128)
  resLoc = inMem vT 0 V128s

  strategy = satUnintSBV yices ["dot"]



prove_Polyval_Horner_AAD_MSG_LENBLK :: IO ()
prove_Polyval_Horner_AAD_MSG_LENBLK =
  newProofSizes "Polyval_Horner_AAD_MSG_LENBLK" strategy $ \aadSize msgSize ->
  Specification
    { specAllocs =
        [ stack
        , vT      := area "T"       RW 16      Bytes
        , vH      := area "H"       RO 16      Bytes
        , vAAD    := area "AAD"     RO aadSize Bytes
        , vPT     := area "PT"      RO msgSize Bytes
        , vLenBlk := area "LEN_BLK" RO 2       QWords
        ]
    , specPres = [ checkPre "Invalid AAD size" (Loc vAADSz === intLit aadSize)
                 , checkPre "Invalid LEN size" (Loc vPTSz  === intLit msgSize)
                 ]
    , specPosts = standardPost ++
                [ checkCryPostDef resLoc
                    "Polyval_Horner_AAD_MSG_def"
                    [ cryArrPre vH      16      Bytes
                    , cryArrPre vAAD    aadSize Bytes
                    , cryArrPre vPT     msgSize Bytes
                    , cryArrPre vLenBlk 2       QWords
                    , cryArrPre vT      16      Bytes
                    ]
                ]

    , specGlobsRO = globals
    }

  where
  vT      = InReg M.RDI
  vH      = InReg M.RSI
  vAAD    = InReg M.RDX
  vAADSz  = InReg M.RCX
  vPT     = InReg M.R8
  vPTSz   = InReg M.R9
  vLenBlk = arg 0

  (arg,stack) = stackAllocArgs 1 (12 + 2 + 1)
  -- Save 12 registers, 16 bytes local (2 qwords); ret for call

  resLoc :: Loc (LLVMPointerType 128)
  resLoc = inMem vT 0 V128s

  strategy = satUnintSBV yices ["dot"]


prove_AES_128_ENC_x4 :: IO ()
prove_AES_128_ENC_x4 =
  newProof "AES_128_ENC_x4" strategy
  Specification
    { specAllocs  = [ stackAlloc 3
                    , vIV   := area "IV"   RO 16        Bytes
                    , vCT   := area "CT"   WO 4         V128s
                    , vKeys := area "Keys" RO (11 * 16) Bytes
                    ]
    , specPres    = [ checkPre "IV not 0 padded"
                         $ Loc (inMem vIV 12 Bytes) === litDWord 0
                    ]
    , specPosts   = standardPost ++
                    [ checkCryPostDef res
                       "AES_128_ENC_x4_def"
                        [ cryArrPre vIV   16        Bytes
                        , cryArrPre vKeys (11 * 16) Bytes
                        ]
                    ]
    , specGlobsRO = globals
    }

  where
  vIV   = InReg M.RDI
  vCT   = InReg M.RSI
  vKeys = InReg M.RDX

  res   = inMem vCT 0 Bytes :: Loc (LLVMPointerType (4 * 128))

  strategy = satUnintSBV z3 [ "aes_round", "aes_final_round" ]



prove_AES_KS_ENC_x1 :: IO ()
prove_AES_KS_ENC_x1 =
  newProof "AES_KS_ENC_x1" strategy
  Specification
    { specAllocs = [ stackAlloc 6
                   , vPT    := area "PT"   RO 16 Bytes
                   , vCT    := area "CT"   WO 16 Bytes
                   , vKeys  := area "Keys" WO 11 V128s
                   , vIKey  := area "IKey" RO 16 Bytes
                   ]
    , specGlobsRO = globals
    , specPres = []
    , specPosts = standardPost ++
        [ checkCryPostDef res1 "AES_KS_ENC_x1_def1" [ cryArrPre vIKey 16 Bytes ]
        , checkCryPostDef res2 "AES_KS_ENC_x1_def2"
            [ cryArrCur vKeys (11 * 16) Bytes
            , cryArrPre vPT   16        Bytes
            ]
        ]
    }

  where
  vPT   = InReg M.RDI
  vCT   = InReg M.RSI
  -- RDX: unused parameter
  vKeys = InReg M.RCX
  vIKey = InReg M.R8

  res1 = inMem vKeys 0 Bytes :: Loc (LLVMPointerType (11 * 128))
  res2 = inMem vCT   0 Bytes :: Loc (LLVMPointerType 128)

  strategy = satABC


prove_ENC_MSG_x4 :: IO ()
prove_ENC_MSG_x4 =
  newProofSizes "ENC_MSG_x4" strategy $ \_aadSize msgSize ->
  Specification
    { specGlobsRO = globals
    , specAllocs =
        [ stackAlloc (10 + 2)
        , vPT   := area "PT"    RO msgSize   Bytes
        , vCT   := area "CT"    WO msgSize   Bytes
        , vTag  := area "TAG"   RO 16        Bytes
        , vKeys := area "Keys"  RO (11 * 16) Bytes
        ]
    , specPres =
        [ checkPre "Invalid message size" (Loc vMsgLen === intLit msgSize) ]
    , specPosts = standardPost ++
        [ checkCryPostDef res "ENC_MSG_def"
            [ cryArrPre vKeys  (11 * 16) Bytes
            , cryArrPre vTag   16        Bytes
            , cryArrPre vPT    msgSize   Bytes
            ]
        ]

    }

  where
  vPT     = InReg M.RDI
  vCT     = InReg M.RSI
  vTag    = InReg M.RDX
  vKeys   = InReg M.RCX
  vMsgLen = InReg M.R8

  -- XXX: The 160 here needs to match `msgSize`
  res = inMem vCT 0 Bytes :: Loc (LLVMPointerType (160 * 8))

  strategy = satUnintSBV z3 [ "aes_round", "aes_final_round" ]




prove_ENC_MSG_x8 :: IO ()
prove_ENC_MSG_x8 =
  let name = "ENC_MSG_x8" in
  doProof name strategy $
  do msgSize <- cryConst "MSG_Size"
     debug ("(Message size = " ++ show msgSize ++ " bytes.)")

     (ptrPT, valPT)     <- freshArray "PT" msgSize Byte Immutable
     valMsgLen          <- literalAt QWord msgSize

     ptrCT              <- allocBytes "CT" Mutable (msgSize .* Byte)
     (ptrTAG, valTag)   <- freshArray "TAG" 16 Byte Immutable
     (ptrKeys, valKeys) <- freshArray "Keys" (11 * 16) Byte Immutable

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
     -- XXX:  SOMEHOW, we can verify this with only 7 instead of 8 words
     -- for the alignment.  This does not seem right. INVESTIGATE.
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


