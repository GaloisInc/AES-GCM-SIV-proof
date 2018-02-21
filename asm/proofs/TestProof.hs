{-# Language OverloadedStrings, RecordWildCards, GADTs #-}
module Main where

import SAWScript.X86
import SAWScript.X86Spec
import Control.Exception(catch)

main :: IO ()
main =
  do gs <- proof linuxInfo "test/a.out" Fun { funName = "f", funSpec = spec }
     print gs
  `catch` \(X86Error e) -> putStrLn e

spec :: FunSpec
spec = FunSpec
  { funPre = pre
  , funPost = \_ -> return ()
  }

pre :: Spec Pre RegAssign
pre =
  do ipFun <- freshRegs
     let valIP = ipFun IP

     let stackSize = 4
     stack <- allocArray infer "Stack" Mutable =<<
              mapM (fresh QWord) (take stackSize
                                   [ "stack_" ++ show n | n <- [ 0 .. ] ])

     rsp <- ptrAdd stack =<<
              literal infer ((fromIntegral stackSize - 1) * 8)
          -- stack grows down; one extra word at the top to return to.

     valGPReg <- setupGPRegs $ \r ->
                    case r of
                      RSP -> gpUse rsp
                      _   -> GPFresh AsBits


     valVecReg <- freshRegs
     valFPReg  <- freshRegs
     valFlag   <- freshRegs
     valX87Status <- freshRegs
     valX87TopF  <- freshRegs
     let valX87Top = valX87TopF X87Top
     valX87Tag <- freshRegs
     return RegAssign { .. }


