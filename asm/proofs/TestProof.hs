{-# Language OverloadedStrings, RecordWildCards, GADTs #-}
module Main where

import SAWScript.X86
import SAWScript.X86Spec

main :: IO ()
main =
  do gs <- proof linuxInfo "test/test.o" Fun { funName = "f", funSpec = spec }
     print gs

spec :: FunSpec
spec = FunSpec
  { funPre = pre
  , funPost = \_ -> return ()
  }

pre =
  do ipFun <- freshRegs
     let valIP = ipFun IP
     valGPReg  <- freshGPRegs (const (GPUse AsBits))
     valVecReg <- freshRegs
     valFPReg  <- freshRegs
     valFlag   <- freshRegs
     valX87Status <- freshRegs
     valX87TopF  <- freshRegs
     let valX87Top = valX87TopF X87Top
     valX87Tag <- freshRegs
     return RegAssign { .. }


