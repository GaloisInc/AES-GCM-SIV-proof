{-# Language OverloadedStrings #-}
module Main where

import SAWScript.X86
import SAWScript.X86Spec

main :: IO ()
main =
  do gs <- proof linuxInfo "test/test.o" Fun { funName = "f", funSpec = spec }
     print gs

spec :: FunSpec
spec = FunSpec
  { funPre =  undefined
  , funPost = \_ -> return ()
  }


