{-# Language DataKinds, RankNTypes, OverloadedStrings, PatternSynonyms #-}
module Main (main) where

import qualified Data.ByteString as BS
import           System.Environment(getArgs)
import           System.Exit(exitFailure)
import           System.IO(hPutStrLn,stderr)
import           Numeric(showHex,readHex)
import           Data.Maybe(isNothing)
import           Data.Char(isSpace)
import           Data.List(nub)
import           System.Process(readProcess)

import Data.ElfEdit(Elf, parseElf, ElfGetResult(..)
                   , findSectionByName, elfSectionData, elfSectionAddr)
import Flexdis86(disassembleBuffer, ppInstruction, disOffset, disInstruction)

main :: IO ()
main =
  do args <- getArgs
     case args of
       file : more ->
         do elf <- getElf file
            case findSectionByName ".text" elf of
              [sec] -> do let base = fromIntegral (elfSectionAddr sec)
                              toAddr i = fromIntegral base + disOffset i
                              see i = "0x" ++ showHex (toAddr i) (": " ++ ins)
                                where ins = maybe "???" (show . ppInstruction base) (disInstruction i)
                              addrs = disassembleBuffer (elfSectionData sec)
                              unkAddrs = map toAddr (filter (isNothing . disInstruction) addrs)
                          case more of
                            _ : _ -> showBad unkAddrs file
                            [] -> mapM_ (putStrLn . see) addrs
              [] -> abort "Failed to find .text section"
              _  -> abort "Multiple .text sections"

       _ -> abort "Usage: <prog> FILENAME"


showBad :: [Int] -> String -> IO ()
showBad bad file =
  do txt <- readProcess "objdump" ["-d", file] ""
     let keep l = case break (== ':') (dropWhile isSpace l) of
                    (as,_:_) | [(a,"")] <- readHex as -> a `elem` bad
                    _        -> False
         toTab = drop 1 . dropWhile (/= '\t')
         instr = takeWhile (not . isSpace) . toTab . toTab
     mapM_ putStrLn $ nub $ map instr $ filter keep $ lines txt


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



