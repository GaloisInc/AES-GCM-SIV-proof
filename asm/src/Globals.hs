{-# Language OverloadedStrings, RecordWildCards #-}
module Globals where

import SAWScript.X86Spec
import SAWScript.X86SpecNew(Unit(..))

-- XXX: we should lookup address from the ELF file.
-- For the time being, we hard-code the locations
setupGlobals :: Spec Pre ()
setupGlobals =
  do let size = 0x403000
     reg <- allocBytes "globals" Immutable (size .* Byte)
     registerRegion 0 reg

     let declare _nm offset ty xs =
           do () <- return (const () (_nm :: String)) -- tmp, to avoid warn
              ptr <- ptrAdd reg (offset .* Byte)
              writeMem ptr =<< mapM (literalAt ty) xs

     declare "poly"       0x400d40 QWord [ 0x1, 0xc200000000000000 ]
     declare "poly"       0x401040 QWord [ 0x1, 0xc200000000000000 ]
     declare "poly"       0x4010c0 QWord [ 0x1, 0xc200000000000000 ]


     declare "OR_MASK"    0x402280 DWord
                            [ 0x00000000,0x00000000,0x00000000,0x80000000 ]

     declare "one"        0x402290 QWord [1,0]
     declare "two"        0x4022a0 QWord [2,0]
     declare "three"      0x4022b0 QWord [3,0]
     declare "four"       0x4022c0 QWord [4,0]

     declare "OR_MASK"    0x402620 DWord
                            [ 0x00000000,0x00000000,0x00000000,0x80000000 ]
     declare "one"        0x402630 QWord [1,0]
     declare "two"        0x402640 QWord [2,0]
     declare "three"      0x402650 QWord [3,0]
     declare "four"       0x402660 QWord [4,0]
     declare "five"       0x402670 QWord [5,0]
     declare "six"        0x402680 QWord [6,0]
     declare "seven"      0x402690 QWord [7,0]
     declare "eight"      0x4026a0 QWord [8,0]



     declare "mask"       0x402b90 DWord [ 0x0c0f0e0d, 0x0c0f0e0d
                                         , 0x0c0f0e0d, 0x0c0f0e0d ]
     declare "con1"       0x402ba0 DWord [ 1, 1, 1, 1 ]
     declare "con2"       0x402bb0 DWord [ 0x1b,0x1b,0x1b,0x1b ]
     declare "con3"       0x402bc0 Byte 
                                  [ -1,-1,-1,-1,-1,-1,-1,-1,4,5,6,7,4,5,6,7]

     declare "one"        0x402bd0 DWord [ 1, 0, 0, 0 ]
     declare "and_mask"   0x402be0 DWord
                                   [ 0,0xffffffff, 0xffffffff, 0xffffffff ]





globals :: [(String,Integer,Unit,[Integer])]
globals =
   [ declare "poly"       0x400c30 QWords [ 0x1, 0xc200000000000000 ]
   -- , declare "poly"       0x401040 QWords [ 0x1, 0xc200000000000000 ]

   , declare "OR_MASK"    0x402280 DWords
                            [ 0x00000000,0x00000000,0x00000000,0x80000000 ]

   , declare "one"        0x402190 QWords [1,0]
   , declare "two"        0x4021a0 QWords [2,0]
   , declare "three"      0x4021b0 QWords [3,0]
   , declare "four"       0x4021c0 QWords [4,0]

   , declare "OR_MASK"    0x402180 DWords
                            [ 0x00000000,0x00000000,0x00000000,0x80000000 ]
   , declare "one"        0x402630 QWords [1,0]
   , declare "two"        0x402640 QWords [2,0]
   , declare "three"      0x402650 QWords [3,0]
   , declare "four"       0x402660 QWords [4,0]
   , declare "five"       0x402670 QWords [5,0]
   , declare "six"        0x402680 QWords [6,0]
   , declare "seven"      0x402690 QWords [7,0]
   , declare "eight"      0x4026a0 QWords [8,0]


   , declare "mask"       0x402a90 DWords [ 0x0c0f0e0d, 0x0c0f0e0d
                                         , 0x0c0f0e0d, 0x0c0f0e0d ]
   , declare "con1"       0x402aa0 DWords [ 1, 1, 1, 1 ]
   , declare "con2"       0x402ab0 DWords [ 0x1b,0x1b,0x1b,0x1b ]
   , declare "con3"       0x402ac0 Bytes
                                  [ -1,-1,-1,-1,-1,-1,-1,-1,4,5,6,7,4,5,6,7]

   , declare "one"        0x402ad0 DWords [ 1, 0, 0, 0 ]
   , declare "and_mask"   0x402ae0 DWords
                                   [ 0,0xffffffff, 0xffffffff, 0xffffffff ]
  ]

  where
  declare a b c d = (a,b,c,d)


