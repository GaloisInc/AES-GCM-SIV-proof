{-# Language OverloadedStrings #-}
module Main where

import Data.ByteString(ByteString)
import qualified Data.ByteString as LBS
import System.Environment(getArgs)
import System.Exit(exitFailure)
import System.IO(hPutStrLn,stderr)
import Control.Monad(unless)

import Flexdis86(disassembleBuffer, DisassembledAddr(..))
import Data.ElfEdit(Elf,ElfGetResult(..), parseElf, findSectionByName
                   , ElfSection(..) )

main :: IO ()
main =
  do args <- getArgs
     case args of
       [ file ] ->
          do bytes <- LBS.readFile file
             case parseElf bytes of

               Elf32Res errs elf32 -> 
                  do unless (null errs) $
                       abort $ unlines $
                                  "Malformed 32-bit elf file" : map show errs
                     withElf elf32

               Elf64Res errs elf64 ->
                  do unless (null errs) $
                        abort $ unlines $
                                  "Malformed 64-bit elf file" : map show errs
                     withElf elf64

               ElfHeaderError _ err ->
                 abort "This does not look like an elf file"


       _ -> abort "Usage: <prog> FILENAME"


abort :: String -> IO a
abort msg = do hPutStrLn stderr msg
               exitFailure

             -- mapM_ print (disassembleBuffer bytes)
withElf :: Elf w -> IO ()
withElf elf =
  case findSectionByName ".text" elf of
    [ sec ] -> withInstructions (disassembleBuffer (elfSectionData sec))
    [] -> abort "Failed to find .text section"
    _  -> abort "Multiple .text sections"

withInstructions :: [DisassembledAddr] -> IO ()
withInstructions = mapM_ print

