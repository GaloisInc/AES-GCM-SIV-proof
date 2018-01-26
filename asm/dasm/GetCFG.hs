{-# Language DataKinds, RankNTypes, OverloadedStrings, PatternSynonyms #-}
module Main (main) where

import qualified Data.Map as Map
import           Data.ByteString(ByteString)
import qualified Data.ByteString.Char8 as BS
import qualified Data.Vector as Vector
import           Data.Maybe(maybeToList)
import           System.Environment(getArgs)
import           System.Exit(exitFailure)
import           System.IO(hPutStrLn,stderr)
import           Control.Lens((^.))
import           Text.PrettyPrint.ANSI.Leijen(pretty)

import Data.Parameterized.Some(Some(..))
import Data.ElfEdit(Elf
                   , parseElf
                   , ElfGetResult(..),
                    steValue, elfSymbolTableEntries,
                    elfSymtab, elfSymbolTableEntries, steName, steType,
                    pattern STT_FUNC)
import Data.Macaw.Memory(Memory, MemSegmentOff,
                           memWord, resolveAbsoluteAddr)
import Data.Macaw.Memory.ElfLoader( LoadOptions(..)
                                  , LoadStyle(..)
                                  , memoryForElf)
import Data.Macaw.Discovery(cfgFromAddrs , DiscoveryState
                           , DiscoveryFunInfo
                           , funInfo, parsedBlocks )
import Data.Macaw.X86(x86_64_linux_info)
import Data.Macaw.X86.ArchTypes(X86_64)

main :: IO ()
main =
  do args <- getArgs
     case args of
       [ file, fun ] ->
         do elf <- getElf file
            mem <- getMemory elf
            case findFun elf mem (BS.pack fun) of
              [off] -> do let disc = getDiscoverState mem off
                              funs = disc ^. funInfo
                          mapM_ dumpFun (Map.toList funs)
              [] -> fail ("Failed to find address for: " ++ show fun)
              xs -> fail $ unlines
                            [ "Found multiple addresses for: " ++ show fun
                            , unwords (map (show . pretty) xs)
                            ]

       _ -> abort "Usage: <prog> FILENAME FUNCTION"

dumpFun :: (MemSegmentOff 64, Some (DiscoveryFunInfo X86_64)) -> IO ()
dumpFun (addr,Some fi) =
  do putStrLn ("Address: " ++ show (pretty addr))
     putStrLn "Blocks:"
     mapM_ printBlock (Map.elems (fi ^. parsedBlocks))

  where
  printBlock bl =
      do putStrLn "--------------------"
         mapM_ putStrLn $ map ("  " ++) $ lines $ show $ pretty bl

findFun :: Elf 64 -> Memory 64 -> ByteString -> [ MemSegmentOff 64 ]
findFun elf mem name =
  [ off | syt <- elfSymtab elf
        , ent <- Vector.toList (elfSymbolTableEntries syt)
        , steName ent == name
        , steType ent == STT_FUNC
        , off <- maybeToList (toOffset (steValue ent)) ]
  where toOffset w = resolveAbsoluteAddr mem (memWord (fromIntegral w))

getElf :: FilePath -> IO (Elf 64)
getElf path =
  do bytes <- BS.readFile path
     case parseElf bytes of
       Elf64Res [] e -> return e
       Elf64Res _ _  -> fail "Parse errors in 64-bit ELF."
       Elf32Res _ _  -> fail "Currently we only support 64-bit ELF."
       ElfHeaderError {} -> fail "Elf header error"

getMemory :: Elf 64 -> IO (Memory 64)
getMemory elf =
  case memoryForElf opts elf of
    Right (_,mem) -> return mem
    Left err      -> fail err
  where
  opts = LoadOptions { loadRegionIndex = 0
                     , loadStyle = LoadBySection
                     , includeBSS = False }

abort :: String -> IO a
abort msg = do hPutStrLn stderr msg
               exitFailure

getDiscoverState :: Memory 64 -> MemSegmentOff 64 -> DiscoveryState X86_64
getDiscoverState mem addr =
  cfgFromAddrs
    x86_64_linux_info
    mem
    Map.empty
    [addr]
    []


