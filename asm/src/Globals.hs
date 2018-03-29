module Globals where

import SAWScript.X86SpecNew(Unit(..))

globals :: [(String,Integer,Unit,[Integer])]
globals =
   [ declare "poly"       0x400a80 QWords [ 0x1, 0xc200000000000000 ]
   , declare "poly"       0x400d80 QWords [ 0x1, 0xc200000000000000 ]

   , declare "OR_MASK"    0x401fc0 DWords
                            [ 0x00000000,0x00000000,0x00000000,0x80000000 ]
   , declare "one"        0x401fd0 QWords [1,0]
   , declare "two"        0x401fe0 QWords [2,0]
   , declare "three"      0x401ff0 QWords [3,0]
   , declare "four"       0x402000 QWords [4,0]


   , declare "OR_MASK"    0x402360 DWords
                            [ 0x00000000,0x00000000,0x00000000,0x80000000 ]
   , declare "one"        0x402370 QWords [1,0]
   , declare "two"        0x402380 QWords [2,0]
   , declare "three"      0x402390 QWords [3,0]
   , declare "four"       0x4023a0 QWords [4,0]
   , declare "five"       0x4023b0 QWords [5,0]
   , declare "six"        0x4023c0 QWords [6,0]
   , declare "seven"      0x4023d0 QWords [7,0]
   , declare "eight"      0x4023e0 QWords [8,0]


   , declare "mask"       0x4028d0 DWords [ 0x0c0f0e0d, 0x0c0f0e0d
                                         , 0x0c0f0e0d, 0x0c0f0e0d ]
   , declare "con1"       0x4028e0 DWords [ 1, 1, 1, 1 ]
   , declare "con2"       0x4028f0 DWords [ 0x1b,0x1b,0x1b,0x1b ]
   , declare "con3"       0x402900 Bytes
                                  [ -1,-1,-1,-1,-1,-1,-1,-1,4,5,6,7,4,5,6,7]

   , declare "one"        0x402910 DWords [ 1, 0, 0, 0 ]
   , declare "and_mask"   0x402920 DWords
                                   [ 0,0xffffffff, 0xffffffff, 0xffffffff ]

  , declare "and_mask_c"  0x0403500 QWords [ 0xffffffffffffffff
                                           , 0x7fffffffffffffff ]

  ]

  where
  declare a b c d = (a,b,c,d)


