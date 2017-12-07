{-# Language DataKinds, RankNTypes, OverloadedStrings, PatternSynonyms #-}
module Main (main) where

import qualified Data.ByteString as BS
import           System.Environment(getArgs)
import           System.Exit(exitFailure)
import           System.IO(hPutStrLn,stderr)

import Data.ElfEdit(Elf, parseElf, ElfGetResult(..)
                   , findSectionByName, elfSectionData)
import Flexdis86(disassembleBuffer)

main :: IO ()
main =
  do args <- getArgs
     case args of
       [ file ] ->
         do elf <- getElf file
            case findSectionByName ".text" elf of
              [sec] -> mapM_ print (disassembleBuffer (elfSectionData sec))
              [] -> abort "Failed to find .text section"
              _  -> abort "Multiple .text sections"

       _ -> abort "Usage: <prog> FILENAME"

abort :: String -> IO a
abort msg = do hPutStrLn stderr msg
               exitFailure

getElf :: FilePath -> IO (Elf 64)
getElf path =
  do bytes <- BS.readFile path
     case parseElf bytes of
       Elf64Res errs elf
          | null errs -> return elf
          | otherwise -> abort "Malfored 64-bit ELF"
       Elf32Res {} -> abort "We only support 32-bite ELF"
       ElfHeaderError _ x -> abort x



