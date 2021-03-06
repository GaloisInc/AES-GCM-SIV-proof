{-# Language OverloadedStrings #-}
module Main where

import System.Exit(exitFailure)
import Control.Exception(SomeException(SomeException),catch)

import SAWScript.X86Spec hiding (cryConst, cryTerm)
import Data.Macaw.X86.X86Reg

import Utils


main :: IO ()
main =
  do fun_GFMUL  <- newProof "_GFMUL" useRME spec_GFMUL
     fun_GFMUL' <- newProof "GFMUL"  useRME spec_GFMUL

     -- used in Decrypt
     _ <- newProofSizes "Polyval_Horner"
            (useSMT ["dot"])
            $ \aadSize _msgSize -> spec_Polyval_Horner "AAD" fun_GFMUL aadSize

     fun_Polyval_Horner_AAD_MSG_LENBLK <-
        newProofSizes "Polyval_Horner_AAD_MSG_LENBLK"
            (useSMT ["dot"])
            $ spec_Polyval_Horner_AAD_MSG_LENBLK fun_GFMUL

     fun_AES_128_ENC_x4 <- newProof "AES_128_ENC_x4"
           (useSMT [ "aes_round", "aes_final_round" ])
           spec_AES_128_ENC_x4

     fun_AES_KS_ENC_x1 <- newProof "AES_KS_ENC_x1" useABC spec_AES_KS_ENC_x1

     fun_ENC_MSG_x4 <- newProofSizes "ENC_MSG_x4"
            (useSMT [ "aes_round", "aes_final_round" ])
            $ \_aadSize msgSize -> spec_ENC_MSG_x4 msgSize

     -- Used for larger sizes
     fun_ENC_MSG_x8 <- newProofSizes "ENC_MSG_x8"
            (useSMT [ "aes_round", "aes_final_round" ])
            $ \_aadSize msgSize -> spec_ENC_MSG_x8 msgSize

     fun_INIT_Htable <- newProof "INIT_Htable"
            (useSMT ["dot"])
            (spec_INIT_Htable fun_GFMUL')

     fun_Polyval_Htable <- newProofSizes "Polyval_Htable"
          useRME
          $ \aadSize _msgSize -> spec_Polyval_Htable "AAD" aadSize

     _fun_Polyval_Htable <- newProofSizes "Polyval_Htable"
          useRME
          $ \_aadSize msgSize -> spec_Polyval_Htable "MSG" msgSize

     _fun_Polyval_Htable <- newProof "Polyval_Htable"
          useRME (spec_Polyval_Htable "BLK" 16)

     _ <- newProofSizes "AES_GCM_SIV_Encrypt"
            (useSMT [ "aes", "ExpandKey"
                               , "dot", "counter_mode" ])
            $ \aadSize msgSize -> spec_AES_GCM_SIV_Encrypt
                                      fun_GFMUL
                                      fun_Polyval_Horner_AAD_MSG_LENBLK
                                      fun_AES_128_ENC_x4
                                      fun_AES_KS_ENC_x1
                                      fun_ENC_MSG_x4
                                      fun_ENC_MSG_x8
                                      fun_INIT_Htable
                                      fun_Polyval_Htable
                                      aadSize msgSize

     return ()
  `catch` \(SomeException e) -> do print e
                                   exitFailure

spec_INIT_Htable :: Integer -> Specification
spec_INIT_Htable gfmul =
  Specification
    { specGlobsRO = []
    , specAllocs  =
        [ stackAlloc 1
        , vH   := area "H"   RO 1  V128s
        , vTab := area "TAB" WO 8  V128s
        ]
    , specPres = []
    , specPosts = standardPost ++
          [ checkCryPointsTo (PreLoc vTab) 8 V128s
             "INIT_Htable_def" [ CryArrPre (PreLoc vH) 1 V128s ]
          ]
    , specCalls =
         [ ("GFMUL", gfmul, const spec_GFMUL) ]
    }
  where
  vTab = InReg RDI
  vH   = InReg RSI



spec_Polyval_Htable :: String -> Integer -> Specification
spec_Polyval_Htable pref size =
  Specification
    { specGlobsRO = []
    , specAllocs =
        [ stackAlloc (12 + 2)
        , vHtable := area "Htbl" RO 8     V128s
        , vT      := area "T"    RW 1     V128s
        , vBuf    := area "Buf"  RO size  Bytes
        ]
    , specPres = [ checkPre "Invalid size" (Loc vSize === intLit size) ]
    , specPosts = standardPost ++
        [ checkCryPointsTo (PreLoc vT) 1 V128s
            ("Polyval_HTable_" ++ pref ++ "_def")
              [ CryArrPre (PreLoc vHtable) 8    V128s
              , CryArrPre (PreLoc vBuf)    size Bytes
              , CryArrPre (PreLoc vT)      1    V128s
              ]
        ]
    , specCalls = []
    }
  where
  vHtable = InReg RDI
  vBuf    = InReg RSI
  vSize   = InReg RDX
  vT      = InReg RCX


spec_GFMUL :: Specification
spec_GFMUL =
  Specification
    { specAllocs  = [ stackAlloc 0 ]
    , specPres    = []
    , specPosts   =
        standardPost ++
        [ checkPreserves h
        , checkPreserves (InReg RAX)
        , checkPreserves (InReg RCX)
        , checkPreserves (InReg RDX)
        , checkPreserves (InReg RDI)
        , checkPreserves (InReg RSI)
        , checkPreserves (InReg R8)
        , checkPreserves (InReg R9)
        , checkPreserves (InReg R10)
        , checkPreserves (InReg R11)
        , checkCryPostDef (Loc res) "dot512" [ cryPre res, cryPre h ]
        ]
    , specGlobsRO = []
    , specCalls = []
    }
  where
  res = InReg (ZMM 0)
  h   = InReg (ZMM 1)



spec_Polyval_Horner ::
  String  {- ^ Prefix to use in spec (should match the size) -} ->
  Integer {- ^ Address of GFMUL -} ->
  Integer {- ^ Input size -} ->
  Specification
spec_Polyval_Horner pref gfmul size =
  Specification
    { specAllocs =
      [ -- Save 10 registers; 16 bytes local (2 qwords); RET for call
        stackAlloc (10 + 2 + 1)

      , vT   := area "T"   RW 1     V128s
      , vH   := area "H"   RO 1     V128s
      , vBuf := area "buf" RO size  Bytes
      ]

    , specPres = [ checkPre ("Input size not " ++ show size)
                            (Loc vSize === intLit size) ]

    , specPosts = standardPost ++
        [ checkCryPointsTo (PreLoc vT) 1 V128s
             ("Polyval_Horner_" ++ pref ++ "_def")
                [ CryArrPre (PreLoc vH)   1    V128s
                , CryArrPre (PreLoc vBuf) size Bytes
                , CryArrPre (PreLoc vT)   1    V128s
                ]
       ]

    , specGlobsRO = []
    , specCalls = [ ("GFMUL", gfmul, const spec_GFMUL) ]
    }
  where
  vT    = InReg RDI
  vH    = InReg RSI
  vBuf  = InReg RDX
  vSize = InReg RCX


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
                [ checkCryPointsTo (PreLoc vT) 1 V128s
                    "Polyval_Horner_AAD_MSG_def"
                    [ CryArrPre (PreLoc vH)      16      Bytes
                    , CryArrPre (PreLoc vAAD)    aadSize Bytes
                    , CryArrPre (PreLoc vPT)     msgSize Bytes
                    , CryArrPre (PreLoc vLenBlk) 2       QWords
                    , CryArrPre (PreLoc vT)      16      Bytes
                    ]
                ]

    , specGlobsRO = []
    , specCalls = [ ("GFMUL", gfmul, const spec_GFMUL) ]
    }

  where
  vT      = InReg RDI
  vH      = InReg RSI
  vAAD    = InReg RDX
  vAADSz  = InReg RCX
  vPT     = InReg R8
  vPTSz   = InReg R9
  vLenBlk = arg 0

  (arg,stack) = stackAllocArgs 1 (12 + 2 + 1)
  -- Save 12 registers, 16 bytes local (2 qwords); ret for call





spec_AES_128_ENC_x4 :: Specification
spec_AES_128_ENC_x4 =
  Specification
    { specAllocs  = [ stackAlloc 3
                    , vIV   := area "IV"   RO 16 Bytes
                    , vCT   := area "CT"   WO 4  V128s
                    , vKeys := area "Keys" RO 11 V128s
                    ]
    , specPres    = [ checkPre "IV not 0 padded"
                         $ Loc (inMem vIV 12 Bytes) === litDWord 0
                    ]
    , specPosts   = standardPost ++
                    [ checkCryPointsTo (PreLoc vCT) 4 V128s
                       "AES_128_ENC_x4_def"
                        [ CryArrPre (PreLoc vIV)   16  Bytes
                        , CryArrPre (PreLoc vKeys) 11  V128s
                        ]
                    ]
    , specGlobsRO = []
    , specCalls = []
    }

  where
  vIV   = InReg RDI
  vCT   = InReg RSI
  vKeys = InReg RDX



spec_AES_KS_ENC_x1 :: Specification
spec_AES_KS_ENC_x1 =
  Specification
    { specAllocs = [ stackAlloc 6
                   , vPT    := area "PT"   RO 16 Bytes
                   , vCT    := area "CT"   WO 16 Bytes
                   , vKeys  := area "Keys" WO 11 V128s
                   , vIKey  := area "IKey" RO 16 Bytes
                   ]
    , specGlobsRO = []
    , specPres = []
    , specPosts = standardPost ++
        [ checkCryPointsTo (PreLoc vKeys) 11 V128s
          "AES_KS_ENC_x1_def1" [ CryArrPre (PreLoc vIKey) 16 Bytes ]

        , checkCryPointsTo (PreLoc vCT) 1 V128s
           "AES_KS_ENC_x1_def2"
              [ CryArrCur (PreLoc vKeys) 11 V128s
              , CryArrPre (PreLoc vPT)   16 Bytes
              ]
        ]
    , specCalls = []
    }

  where
  vPT   = InReg RDI
  vCT   = InReg RSI
  -- RDX: unused parameter
  vKeys = InReg RCX
  vIKey = InReg R8



spec_ENC_MSG_x4 ::
  Integer {- ^ Message size -} ->
  Specification
spec_ENC_MSG_x4 msgSize =
  Specification
    { specGlobsRO = []
    , specAllocs =
        [ stackAlloc (10 + 2)
        , vPT   := area "PT"    RO msgSize   Bytes
        , vCT   := area "CT"    WO msgSize   Bytes
        , vTag  := area "TAG"   RO 16        Bytes
        , vKeys := area "Keys"  RO 11        V128s
        ]
    , specPres =
        [ checkPre "Invalid message size" (Loc vMsgLen === intLit msgSize) ]
    , specPosts = standardPost ++
        [ checkCryPointsTo (PreLoc vCT) msgSize Bytes
          "ENC_MSG_def" [ CryArrPre (PreLoc vKeys)  11        V128s
                        , CryArrPre (PreLoc vTag)   16        Bytes
                        , CryArrPre (PreLoc vPT)    msgSize   Bytes
                        ]
        ]
    , specCalls = []
    }

  where
  vPT     = InReg RDI
  vCT     = InReg RSI
  vTag    = InReg RDX
  vKeys   = InReg RCX
  vMsgLen = InReg R8


spec_ENC_MSG_x8 :: Integer -> Specification
spec_ENC_MSG_x8 msgSize =
  Specification
    { specGlobsRO = []
    , specAllocs  =
        [ stackAlloc (12 + 16 + 8 + 2)
        , vPT   := area "PT"   RO msgSize Bytes
        , vCT   := area "CT"   WO msgSize Bytes
        , vTAG  := area "TAG"  RO 16      Bytes
        , vKeys := area "Keys" RO 11      V128s
        ]
    , specPres = [ checkPre "Invalid message lenght"
                            (Loc vMsgL === intLit msgSize) ]
    , specPosts = standardPost ++
        [ checkCryPointsTo (PreLoc vCT) msgSize Bytes
            "ENC_MSG_def" [ CryArrPre (PreLoc vKeys)  11        V128s
                          , CryArrPre (PreLoc vTAG)   16        Bytes
                          , CryArrPre (PreLoc vPT)    msgSize   Bytes
                          ]
        ]
    , specCalls = []
    }

  where
  vPT   = InReg RDI
  vCT   = InReg RSI
  vTAG  = InReg RDX
  vKeys = InReg RCX
  vMsgL = InReg R8






spec_AES_GCM_SIV_Encrypt ::
  Integer -> Integer -> Integer -> Integer ->
  Integer -> Integer -> Integer -> Integer ->
  Integer -> Integer ->
  Specification
spec_AES_GCM_SIV_Encrypt
  fun_GFMUL
  fun_Polyval_Horner_AAD_MSG_LENBLK
  fun_AES_128_ENC_x4
  fun_AES_KS_ENC_x1
  fun_ENC_MSG_x4
  fun_ENC_MSG_x8
  fun_INIT_Htable
  fun_Polyval_Htable
  aadSize msgSize =

  Specification
  { specGlobsRO = []
  , specAllocs =
      [ stack
      , vCtx  := area "Ctx" RO 40        V128s
      , vPT   := area "PT"  RO msgSize   Bytes
      , vCT   := area "CT"  WO msgSize   Bytes
      , vTag  := area "TAG" WO 16        Bytes
      , vAAD  := area "AAD" RO aadSize   Bytes
      , vIV   := area "IV"  RO 12        Bytes
      ]
  , specPres = [ checkPre "Invalid AAD size" (Loc vAADSz === intLit aadSize)
               , checkPre "Invalid MSG size" (Loc vMsgSz === intLit msgSize)
               ]
  , specPosts = standardPost ++
{-
                [ checkCryPointsTo (PreLoc vTag) 1 V128s
                  "TEST"
                  [ CryArrPre (PreLoc vCtx)   11        V128s
                  , CryArrPre (PreLoc vIV)    12        Bytes
                  , CryArrPre (PreLoc vAAD)   aadSize   Bytes
                  , CryArrPre (PreLoc vPT)    msgSize   Bytes
                  ]


                ] -}

                [ checkCryPointsTo (PreLoc vTag) 1 V128s
                  "AES_GMC_SIV_Encrypt_TAG_def"
                      [ CryArrPre (PreLoc vCtx)   11        V128s
                      , CryArrPre (PreLoc vIV)    12        Bytes
                      , CryArrPre (PreLoc vAAD)   aadSize   Bytes
                      , CryArrPre (PreLoc vPT)    msgSize   Bytes
                      ]

                , checkCryPointsTo (PreLoc vCT) msgSize Bytes
                  "AES_GMC_SIV_Encrypt_CT_def"
                      [ CryArrPre (PreLoc vCtx)   11        V128s
                      , CryArrPre (PreLoc vIV)    12        Bytes
                      , CryArrPre (PreLoc vAAD)   aadSize   Bytes
                      , CryArrPre (PreLoc vPT)    msgSize   Bytes
                      ]
                ]

  , specCalls =
      [ ( "AES_128_ENC_x4"
        , fun_AES_128_ENC_x4
        , const spec_AES_128_ENC_x4
        )

      , ( "Polyval_Horner_AAD_MSG_LENBLK"
        , fun_Polyval_Horner_AAD_MSG_LENBLK
        , const $ spec_Polyval_Horner_AAD_MSG_LENBLK fun_GFMUL aadSize msgSize
        )

      , ( "AES_KS_ENC_x1"
        , fun_AES_KS_ENC_x1
        , const spec_AES_KS_ENC_x1
        )

      , ( "ENC_MSG_x4"
        , fun_ENC_MSG_x4
        , const $ spec_ENC_MSG_x4 msgSize
        )

      , ( "ENC_MSG_x8"
        , fun_ENC_MSG_x8
        , const $ spec_ENC_MSG_x8 msgSize
        )

      , ( "INIT_Htable"
        , fun_INIT_Htable
        , const $ spec_INIT_Htable fun_GFMUL
        )

      , ( "Polyval_Htable"
        , fun_Polyval_Htable
        , \e -> case e of
                  0 -> spec_Polyval_Htable "call_AAD" aadSize
                  1 -> spec_Polyval_Htable "call_MSG" msgSize
                  2 -> spec_Polyval_Htable "call_BLK" 16
                  _ -> error "Unexpecte call to Polyval_Htable"
        )
      ]
  }

  where
  vCtx    = InReg RDI
  vCT     = InReg RSI
  vTag    = InReg RDX
  vAAD    = InReg RCX
  vPT     = InReg R8
  vAADSz  = InReg R9
  vMsgSz  = arg 0
  vIV     = arg 1

  -- (arg,stack) = stackAllocArgs 2 62
  (arg,stack) = stackAllocArgs 2 200


