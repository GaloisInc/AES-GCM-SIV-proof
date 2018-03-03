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

     declare "con1"     0x402ba0 DWord [ 1, 1, 1, 1 ]
     declare "one"      0x402bd0 DWord [ 1, 0, 0, 0 ]
     declare "and_mask" 0x402be0 DWord [ 0,0xffffffff, 0xffffffff, 0xffffffff ]





