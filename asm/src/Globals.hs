{-# Language OverloadedStrings, RecordWildCards #-}
module Globals where

import SAWScript.X86Spec

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
     declare "mask"       0x402b90 DWord [ 0x0c0f0e0d, 0x0c0f0e0d
                                         , 0x0c0f0e0d, 0x0c0f0e0d ]
     declare "con1"       0x402ba0 DWord [ 1, 1, 1, 1 ]
     declare "con2"       0x402bb0 DWord [ 0x1b,0x1b,0x1b,0x1b ]
     declare "shuff_mask" 0x402bc0 QWord
                                   [0x0f0f0f0f0f0f0f0f, 0x0f0f0f0f0f0f0f0f]
     declare "one"        0x402bd0 DWord [ 1, 0, 0, 0 ]
     declare "and_mask"   0x402be0 DWord
                                   [ 0,0xffffffff, 0xffffffff, 0xffffffff ]





