{-# LANGUAGE MagicHash, BangPatterns, ScopedTypeVariables #-}
module Main where

import Control.Monad (when)
import Data.Vector hiding (span, tail, (++), zipWith, map, or, filter, length)
import Data.Bits
import Data.List
import Data.Word
import GHC.Types

import Debug.Trace

import System.Random

boardSize = 19

wordSize = 8
pointsPerWord = wordSize `div` 2

type GameBoard = Vector Word8

initialBoard :: GameBoard
initialBoard = generate (1 + boardSize*boardSize `div` pointsPerWord) (const 0)

{-# INLINE lin #-}
lin i j = i * boardSize + j

{-# INLINE byteOffset #-}
byteOffset n = n `div` pointsPerWord
{-# INLINE haNibOffset #-}
haNibOffset n = n `mod` pointsPerWord

valueAt i j board =
    let haNibNum = lin i j in
    let item = board ! (haNibNum `div` 4) in
    item `shiftR` ((haNibNum `mod` 4) * 2) .&. haNibMask

isClear i j board = valueAt i j board == 0
isOn i j board = valueAt i j board == haNibMask

haNibMask :: Word8
haNibMask = 0x03

{-# INLINE setWhite #-}
setWhite i j board =
    let haNib = lin i j in
    let bytNum = haNib `div` 4 in
    board // [(bytNum, (whiteInByte haNib) .|. (board ! bytNum))]

{-# INLINE setBlack #-}
setBlack i j board =
    let haNib = lin i j in
    let bytNum = haNib `div` 4 in
    board // [(bytNum, (blackInByte haNib) .|. (board ! bytNum))]

{-# INLINE setClear #-}
setClear i j board =
    let haNib = lin i j in
    let bytNum = haNib `div` 4 in
    board // [(bytNum, (clearMask haNib) .&. (board ! bytNum))]

{-# INLINE setOn #-}
setOn i j board =
    let haNib = lin i j in
    let bytNum = haNib `div` 4 in
    board // [(bytNum, (onBits haNib) .|. (board ! bytNum))]

onBits haNib =
    mask (haNib `mod` 4)
      where {-# INLINE mask #-}
            mask 0 = 0x03
            mask 1 = 0x0c
            mask 2 = 0x30
            mask 3 = 0xc0

{-# INLINE whiteInByte #-}
whiteInByte haNib = 
    mask (haNib `mod` 4)
      where {-# INLINE mask #-}
            mask 0 = 0x01
            mask 1 = 0x04
            mask 2 = 0x10
            mask 3 = 0x40

whiteHaNib = 0x01
blackHaNib = 0x02

{-# INLINE blackInByte #-}
blackInByte haNib = 
    mask (haNib `mod` 4)
      where mask 0 = 0x02
            mask 1 = 0x08
            mask 2 = 0x20
            mask 3 = 0x80

{-# INLINE clearMask #-}
clearMask haNib = 
    mask (haNib `mod` 4)
      where mask 0 = 0xfc
            mask 1 = 0xf3
            mask 2 = 0xcf
            mask 3 = 0x3f

displayBoard board =
   unlines [[charFor (valueAt i j board) | i <- [0..18]] | j <- [0..18]]
      where charFor 0 = '.'
            charFor 1 = 'O'
            charFor 2 = '#'
            charFor 3 = '%'

identifyString board forBlack i j =
  let desired = if forBlack then blackHaNib else whiteHaNib in
  let stringMap = initialBoard in
  let loop [] stringMap = stringMap
      loop ((i, j):todo) stringMap =
                  if valueAt i j stringMap == 0x3 then loop todo stringMap else
                  if valueAt i j board == desired then
                      let stringMap' = setOn i j stringMap in
                      loop (allAdj i j++todo) stringMap'
                  else loop todo stringMap
  in
    loop [(i, j)] stringMap

isEmptyString s = Data.List.and [isClear i j s | i <- [0..18], j <- [0..18]]

{-# INLINE allAdj #-}    
allAdj i j = filter inBounds [(i+1,j), (i,j+1), (i-1,j), (i,j-1)]
    where inBounds (i, j) = 0 <= i && i < boardSize && 0 <= j && j < boardSize

liberties stringMap board forBlack =
  countTrue [isClear i j board && someAdjOn i j stringMap | i <- [0..18], j <- [0..18]]
    where someAdjOn i j stringMap = or [isOn i' j' stringMap | (i', j') <- allAdj i j]
          countTrue xs = length [x | x <- xs, x]

-- User Interface

decodeMove :: String -> Maybe (Int, Int)
decodeMove str =
    if str == "pass" then Nothing else
    let (a,b) = Prelude.span (/=',') str in
    Just (read a, read (Prelude.tail b))

diagnose board forBlack i j =
    let stringMap = identifyString board forBlack i j in
    let l = liberties stringMap board forBlack in
    do putStrLn $ unlines $ lines (displayBoard board :: String)
                            `beside` lines (displayBoard stringMap)
       putStrLn $ "String has " ++ show l ++ " liberties"

type StringMap = GameBoard

findAdjacentDeadStrings board i j oppBlack =
      do candidate@(i,j) <- allAdj i j
         let string = identifyString board oppBlack i j
         if not (isEmptyString string) && 0 == liberties string board oppBlack
         then return string else []

-- TODO: Count and report number of captures.
killAdjacentDeadStrings board i j oppBlack =
    let deadStrings = findAdjacentDeadStrings board i j oppBlack
    in
      Data.List.foldl' killString board deadStrings

killString board string =
  let boardIJs = [(i,j) | i <- [0..18], j <- [0..18]] in
  let killIJs = [(i, j) | (i, j) <- boardIJs, isOn i j string] in
  Data.List.foldl' (\b (i,j) -> setClear i j b) board killIJs

loop blackMove pass1 board (i,j) = do
    diagnose board (not blackMove) i j
    --putStrLn $ displayBoard board
    putStr "> "
    move <- getLine
    case decodeMove move of
      Nothing -> if pass1 then putStrLn "Done!" else loop (not blackMove) True board (0,0)
      Just (i, j) -> do
        when (not (isClear i j board)) (do putStrLn "ILLEGAL MOVE"; loop blackMove pass1 board (i,j))
        let newBoard = (if blackMove then setBlack else setWhite) i j board
        let newBoard2 = killAdjacentDeadStrings newBoard i j (not blackMove)
        loop (not blackMove) pass1 newBoard2 (i,j)

play = 
   loop True False initialBoard (0,0)

-- Got 154321 ops per second with -O3 and inlining.
benchmark 0 board = return board
benchmark count board =
  do x <- randomRIO (0,18)
     y <- randomRIO (0,18)
     b <- randomRIO (0,2::Int)
     let f = case b of 0 -> setWhite ; 1 -> setBlack ; 2 -> setClear
     let !newBoard = f x y board
     benchmark (count-1) newBoard

main = do
  b <- benchmark 100000 initialBoard
  putStrLn $ displayBoard b
  return ()

beside :: [String] -> [String] -> [String]
beside x y = zipWith (++) x (map (' ':) y)
