module Sizes where

import SAWScript.X86Spec

aad_size :: Bytes
aad_size = 17


block_size :: Bytes
block_size = 16

aad_size_blocks :: Integer
aad_size_blocks = bytesToBlocks (bytesToInteger aad_size)

-- A block is 16 bytes (128 bits)
bytesToBlocks :: Integer -> Integer
bytesToBlocks n = (n + (b-1)) `div` b
  where
  b = bytesToInteger block_size

