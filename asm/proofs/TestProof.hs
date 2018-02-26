{-# Language OverloadedStrings, RecordWildCards, GADTs #-}
module Main where

import SAWScript.X86
import SAWScript.X86Spec
import Control.Exception(catch)

main :: IO ()
main =
  do gs <- proof linuxInfo "test/a.out"
            Fun { funName = "f"
                , funSpec = FunSpec { spec     = pre
                                    , cryDecls = Just "test/spec.cry" }
                }
     print gs
  `catch` \(X86Error e) -> putStrLn e



-- | Allocate the stack, and return the value for RSP, the return address.
setupStack :: Spec Pre (Value APtr, Value AQWord)
setupStack =
  do -- (smaller) DWord,DWord,space_to_save_rbp(QWord); ret(QWord) (larger)
     stack <- allocBytes "stack" Mutable (3 .* QWord)

     ret  <- fresh QWord "ret"
     p    <- ptrAdd stack (2 .* QWord)
     writeMem p ret

     return (p, ret)


pre :: Spec Pre (RegAssign, Spec Post ())
pre =
  do ipFun <- freshRegs
     let valIP = ipFun IP

     (rsp,ret) <- setupStack
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
     let r = RegAssign { .. }
     let post =
           do preserveGP r RBX
              preserveGP r RBP
              preserveGP r R12
              preserveGP r R13
              preserveGP r R14
              preserveGP r R15

              expectRSP <- ptrAdd rsp (1 .* QWord)
              expectSame "RSP" expectRSP =<< getReg (RSP,AsPtr)

              expectSame "IP" ret =<< getReg IP

     t <- cryTerm "x"

     return (r,post)


