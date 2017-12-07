{-# Language DataKinds, RankNTypes, OverloadedStrings, PatternSynonyms #-}
module Main where

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
import Data.ElfEdit(Elf, SomeElf(..),
                    steValue, elfSymbolTableEntries,
                    elfSymtab, elfSymbolTableEntries, steName, steType,
                    pattern STT_FUNC)
import Data.Macaw.Memory(Memory, MemSegmentOff,
                           memWord, resolveAbsoluteAddr)
import Data.Macaw.Memory.ElfLoader( LoadOptions(..)
                                  , LoadStyle(..)
                                  , memoryForElf, readElf)
import Data.Macaw.Discovery(cfgFromAddrs , DiscoveryState, emptySymbolAddrMap
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
  do elf <- readElf path
     case elf of
       Elf64 e -> return e
       Elf32 _ -> fail "Currently we only support 64-bit ELF."

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
    emptySymbolAddrMap
    [addr]
    []




{-

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


             -- mapM_ print (disassembleBuffer bytes)
withElf :: Elf w -> IO ()
withElf elf =
  case findSectionByName ".text" elf of
    [ sec ] -> withInstructions (disassembleBuffer (elfSectionData sec))
    [] -> abort "Failed to find .text section"
    _  -> abort "Multiple .text sections"

withInstructions :: [DisassembledAddr] -> IO ()
withInstructions = mapM_ print
-}
