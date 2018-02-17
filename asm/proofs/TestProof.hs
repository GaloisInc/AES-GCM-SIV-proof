{-# Language OverloadedStrings #-}
module Main where

import SAWScript.X86
import SAWScript.X86Spec

main :: IO ()
main = proof linuxInfo "a.out" Fun { funName = "f", funSpec = spec }

spec :: FunSpec
spec = FunSpec
  { funPre =  undefined
  , funPost = \_ -> return ()
  }


