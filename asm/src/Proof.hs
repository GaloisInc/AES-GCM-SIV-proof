{-# Language OverloadedStrings, DataKinds, TypeOperators #-}
module Main where

import GHC.TypeLits(type (*))

import SAWScript.Prover.SBV(satUnintSBV,z3,yices)
import SAWScript.Prover.RME(satRME)
import SAWScript.Prover.ABC(satABC)

import SAWScript.X86Spec.Memory

import SAWScript.X86SpecNew hiding (cryConst, cryTerm)
import qualified Data.Macaw.X86.X86Reg as M


import Utils
import Globals


{-
NOTE: all the proofs have some extra preservation post-conditions.
The reason these are there is due to some limitiation in our post-condition
language.  In particular, we have no way to refer to a location in memory
in the post condition, as seen through a register in the pre-condition.

As it happens, all functions preserve the value of the register containing
the original pointer.  So, we just prove that this is the case, and then
we use the value of the register from the post condition.

This is something that should be fixed, eventually.
-}


main :: IO ()
main =
  do {-gfmul <- newProof "_GFMUL" satRME spec_GFMUL

     _ <- newProofSizes "Polyval_Horner"
            (satUnintSBV yices ["dot"])
            $ \aadSize _msgSize -> spec_Polyval_Horner gfmul aadSize

     _ <- newProofSizes "Polyval_Horner_AAD_MSG_LENBLK"
            (satUnintSBV yices ["dot"])
            $ spec_Polyval_Horner_AAD_MSG_LENBLK gfmul


     _ <- newProof "AES_128_ENC_x4"
           (satUnintSBV z3 [ "aes_round", "aes_final_round" ])
           spec_AES_128_ENC_x4
     _ <- newProof "AES_KS_ENC_x1" satABC spec_AES_KS_ENC_x1

     _ <- newProofSizes "ENC_MSG_x4"
            (satUnintSBV z3 [ "aes_round", "aes_final_round" ])
            $ \_aadSize msgSize -> spec_ENC_MSG_x4 msgSize
    -}

     _ <- newProofSizes "AES_GCM_SIV_Encrypt"
            (satUnintSBV z3 [ "aes_round", "aes_final_round" ])
            $ \aadSize msgSize -> spec_AES_GCM_SIV_Encrypt aadSize msgSize

     -- prove_INIT_Htable
     -- prove_Polyval_Htable
     -- prove_ENC_MSG_x8



     return ()


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


spec_GFMUL :: Specification
spec_GFMUL =
  Specification
    { specAllocs  = [ stackAlloc 0 ]
    , specPres    = []
    , specPosts   =
        standardPost ++
        [ checkPreserves h
        , checkPreserves (InReg M.RAX)
        , checkPreserves (InReg M.RCX)
        , checkPreserves (InReg M.RDX)
        , checkPreserves (InReg M.RDI)
        , checkPreserves (InReg M.RSI)
        , checkPreserves (InReg M.R8)
        , checkPreserves (InReg M.R9)
        , checkPreserves (InReg M.R10)
        , checkPreserves (InReg M.R11)
        , checkCryPostDef (Loc res) "dot256" [ cryPre res, cryPre h ]
        ]
    , specGlobsRO = globals
    , specCalls = []
    }
  where
  res = InReg (M.YMM 0)
  h   = InReg (M.YMM 1)



spec_Polyval_Horner ::
  Integer {- ^ Address of GFMUL -} ->
  Integer {- ^ Input size -} ->
  Specification
spec_Polyval_Horner gfmul size =
  Specification
    { specAllocs =
      [ -- Save 10 registers; 16 bytes local (2 qwords); RET for call
        stackAlloc (10 + 2 + 1)

      , vT   := area "T"   RW 16    Bytes
      , vH   := area "H"   RO 16    Bytes
      , vBuf := area "buf" RO size  Bytes
      ]

    , specPres = [ checkPre ("Input size not " ++ show size)
                            (Loc vSize === intLit size) ]

    , specPosts = standardPost ++
        [ checkPreserves vT
        , checkCryPostDef (Loc resLoc)
             "Polyval_Horner_def"
                [ cryArrPre vH   16   Bytes
                , cryArrPre vBuf size Bytes
                , cryArrPre vT   16   Bytes
                ]
       ]

    , specGlobsRO = globals
    , specCalls = [ ("GFMUL", gfmul, spec_GFMUL) ]
    }
  where
  vT    = InReg M.RDI
  vH    = InReg M.RSI
  vBuf  = InReg M.RDX
  vSize = InReg M.RCX

  resLoc :: Loc (LLVMPointerType 128)
  resLoc = inMem vT 0 V128s


spec_Polyval_Horner_AAD_MSG_LENBLK ::
  Integer {- ^ Address of GFMUL -} ->
  Integer {- ^ AAD size -} ->
  Integer {- ^ message size -} ->
  Specification
spec_Polyval_Horner_AAD_MSG_LENBLK gfmul aadSize msgSize =
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
                [ checkPreserves vT
                , checkCryPostDef (Loc resLoc)
                    "Polyval_Horner_AAD_MSG_def"
                    [ cryArrPre vH      16      Bytes
                    , cryArrPre vAAD    aadSize Bytes
                    , cryArrPre vPT     msgSize Bytes
                    , cryArrPre vLenBlk 2       QWords
                    , cryArrPre vT      16      Bytes
                    ]
                ]

    , specGlobsRO = globals
    , specCalls = [ ("GFMUL", gfmul, spec_GFMUL) ]
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






spec_AES_128_ENC_x4 :: Specification
spec_AES_128_ENC_x4 =
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
                    [ checkPreserves vCT
                    , checkCryPostDef (Loc res)
                       "AES_128_ENC_x4_def"
                        [ cryArrPre vIV   16        Bytes
                        , cryArrPre vKeys (11 * 16) Bytes
                        ]
                    ]
    , specGlobsRO = globals
    , specCalls = []
    }

  where
  vIV   = InReg M.RDI
  vCT   = InReg M.RSI
  vKeys = InReg M.RDX

  res   = inMem vCT 0 Bytes :: Loc (LLVMPointerType (4 * 128))




spec_AES_KS_ENC_x1 :: Specification
spec_AES_KS_ENC_x1 =
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
        [ checkPreserves vKeys
        , checkPreserves vCT
        , checkCryPostDef (Loc res1)
                          "AES_KS_ENC_x1_def1" [ cryArrPre vIKey 16 Bytes ]
        , checkCryPostDef (Loc res2)
                          "AES_KS_ENC_x1_def2"
            [ cryArrCur vKeys (11 * 16) Bytes
            , cryArrPre vPT   16        Bytes
            ]
        ]
    , specCalls = []
    }

  where
  vPT   = InReg M.RDI
  vCT   = InReg M.RSI
  -- RDX: unused parameter
  vKeys = InReg M.RCX
  vIKey = InReg M.R8

  res1 = inMem vKeys 0 Bytes :: Loc (LLVMPointerType (11 * 128))
  res2 = inMem vCT   0 Bytes :: Loc (LLVMPointerType 128)



spec_ENC_MSG_x4 ::
  Integer {- ^ Message size -} ->
  Specification
spec_ENC_MSG_x4 msgSize =
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
        [ checkPreserves vCT
        , checkCryPostDef (Loc res) "ENC_MSG_def"
            [ cryArrPre vKeys  (11 * 16) Bytes
            , cryArrPre vTag   16        Bytes
            , cryArrPre vPT    msgSize   Bytes
            ]
        ]
    , specCalls = []
    }

  where
  vPT     = InReg M.RDI
  vCT     = InReg M.RSI
  vTag    = InReg M.RDX
  vKeys   = InReg M.RCX
  vMsgLen = InReg M.R8

  -- XXX: The 24 here needs to match `msgSize`
  res = inMem vCT 0 Bytes :: Loc (LLVMPointerType (24 * 8))





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

{-
  ( RDI    AES_GCM_SIV_CONTEXT* ctx
  , RSI    uint8_t* CT
  , RDX    uint8_t* TAG
  , RCX    const uint8_t* AAD
  , R8     const uint8_t* PT
  , R9     L1
  , SP(1): size_t L2
  , SP(2): const uint8_t* IV
  , (unused) const uint8_t* KEY
  );
-}

spec_AES_GCM_SIV_Encrypt aadSize msgSize =
  Specification
  { specGlobsRO = globals
  , specAllocs =
      [ stack
      -- + space for nr + spece for Htbl
      , vCtx  := area "Ctx" RO (16 * 15) Bytes
      , vPT   := area "PT"  RO msgSize   Bytes
      , vCT   := area "CT"  WO msgSize   Bytes
      , vTag  := area "TAG" WO 16        Bytes
      , vAAD  := area "AAD" RO aadSize   Bytes
      , vIV   := area "IV"  RO 12        Bytes
      ]
  , specPres = [ checkPre "Invalid AAD size" (Loc vAADSz === intLit aadSize)
               , checkPre "Invalid MSG size" (Loc vMsgSz === intLit msgSize)
               ]
  , specPosts = standardPost ++ [ ]
  , specCalls =
      -- [ ("AES_128_ENC_x4", 0x402f66, spec_AES_128_ENC_x4)
      [ ("AES_128_ENC_x4", 0x4030e6, spec_AES_128_ENC_x4)
      ]
  }

  where
  vCtx    = InReg M.RDI
  vCT     = InReg M.RSI
  vTag    = InReg M.RDX
  vAAD    = InReg M.RCX
  vPT     = InReg M.R8
  vAADSz  = InReg M.R9
  vMsgSz  = arg 0
  vIV     = arg 1

  (arg,stack) = stackAllocArgs 2 100
  -- (arg,stack) = stackAllocArgs 2 0x58



