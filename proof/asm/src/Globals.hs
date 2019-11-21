{-# Language OverloadedStrings #-}
module Globals where

import Data.ByteString(ByteString)
import SAWScript.X86Spec(Unit(..))

globals :: [(ByteString,Integer,Unit)]
globals =
   [ declare "poly"     2  QWords
   , declare "OR_MASK"  4  DWords

   , declare "one"      2  QWords
   , declare "two"      2  QWords
   , declare "three"    2  QWords
   , declare "four"     2  QWords
   , declare "five"     2  QWords
   , declare "six"      2  QWords
   , declare "seven"    2  QWords
   , declare "eight"    2  QWords

   , declare "mask"     4  DWords

   , declare "con1"     4  DWords
   , declare "con2"     4  DWords
   , declare "con3"     16 Bytes

   , declare "and_mask"  4 DWords

   , declare "_IO_stdin_used"  4 QWords -- hmm
   ]
  where
  declare x y z = (x,y,z)

