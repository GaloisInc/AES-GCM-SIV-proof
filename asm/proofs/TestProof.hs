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
  , funPost = post
  }

(.*) :: SizeOf t => Integer -> t -> Bytes
n .* t = toBytes (n * bytesToInteger (sizeOf t))

-- | Allocate the stack, and return the value for RSP
setupStack :: Spec Pre (Value APtr)
setupStack =
  do -- (smaller) local,local,space_to_save_rbp; ret (larger)
     stackSize <- literal (bytesToInteger (4 .* QWord))
     stack <- allocBytes "stack" Mutable stackSize

     ret  <- fresh QWord "ret"

     p <- ptrAdd stack (3 .* QWord)
     writeMem p ret

     return p



pre :: Spec Pre RegAssign
pre =
  do ipFun <- freshRegs
     let valIP = ipFun IP

     rsp <- setupStack
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


post :: RegAssign -> Spec Post ()
post r = return ()



