{-# LANGUAGE MagicHash, BangPatterns, ScopedTypeVariables #-}
module Main where

import Control.Monad (when)
import Data.Vector hiding (span, tail, (++), zipWith, map, or, filter, length, foldl')
import qualified Data.Vector
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

displayBoardSized n board =
   unlines [[charFor (valueAt i j board) | i <- [0..n-1]] | j <- [0..n-1]]
      where charFor 0 = '.'
            charFor 1 = 'O'
            charFor 2 = '#'
            charFor 3 = '%'

displayBoard :: GameBoard -> String
displayBoard board = displayBoardSized 19 board

-- TODO: This must be extremely slow! Come up with a cleverer search.
allStrings board =
  Data.List.concat [identifyStringAsColored board i j | i <- [0..18], j <- [0..18]]

-- | Returns a list of pairs (isBlack, stringMap) indicating a stringmap
-- at the given point and whether it is black or white.
identifyStringAsColored board i j =
  case valueAt i j board of
    0x01 -> [(False, identifyString board False i j)]
    0x02 -> [(True, identifyString board True i j)]
    _ -> []

emptyStringMap = initialBoard

identifyString board forBlack i j =
  let desired = if forBlack then blackHaNib else whiteHaNib in
  let stringMap = emptyStringMap in
  -- Essentially a dfs with a stack for nodes to visit.
  let loop [] stringMap = stringMap
      loop ((i, j):todo) stringMap =
                  if valueAt i j stringMap == 0x3 then loop todo stringMap else
                  if valueAt i j board == desired then
                      let stringMap' = setOn i j stringMap in
                      loop (allAdj i j++todo) stringMap'
                  else loop todo stringMap
  in
    loop [(i, j)] stringMap

flood board okPred iI jJ =
  let stringMap = emptyStringMap in
  -- Essentially a dfs with a stack for nodes to visit.
  let loop [] stringMap = if isEmptyString stringMap then Nothing else Just stringMap
      loop ((i, j):todo) stringMap =
                  if atEdge (i, j) then debug ("flood from " ++ show (iI,jJ) ++ " hit edge, discarding") Nothing else
                  if valueAt i j stringMap == 0x3 then loop todo stringMap else
                  if okPred (valueAt i j board) then
                      debug ("flood at " ++ show(i,j) ++ " ok, continuing") $
                      let stringMap' = setOn i j stringMap in
                      loop (allAdj i j++todo) stringMap'
                  else 
                      debug ("failed predicate at " ++ show(i,j) ++ " ignoring") $
                      loop todo stringMap
  in
    loop [(iI, jJ)] stringMap

atEdge (i, j) = i == 0 || j == 0 || i == boardSize-1 || j == boardSize-1

identifyGroup board forBlack i j =
  let desired = if forBlack then blackHaNib else whiteHaNib in
  let stringMap = emptyStringMap in
  -- Essentially a dfs with a stack for nodes to visit.
  let loop [] stringMap = stringMap
      loop ((i, j):todo) stringMap =
                  if valueAt i j stringMap == 0x3 then loop todo stringMap else
                  if valueAt i j board == desired then
                      let stringMap' = setOn i j stringMap in
                      loop (seNeighWeak i j++todo) stringMap'
                  else loop todo stringMap
  in
    loop [(i, j)] stringMap

unionStringMaps a b =
  Data.Vector.zipWith (.|.) a b

findAllStrings board =
    let boardPoints = [(i, j) | i <- [0..18], j <- [0..18]] in
    let (_, results) = 
          foldl' (\(masterMap, results) (i, j) -> 
                  if isClear i j masterMap then
                    case identifyStringAsColored board i j of
                      [] -> (masterMap, results)
                      [(isBlack, newString)] -> 
                        if isEmptyString newString then (masterMap, results)
                        else
                          (unionStringMaps masterMap newString,
                           newString:results)
                  else
                     (masterMap, results)
              )
              (emptyStringMap, []) boardPoints
    in
      results

isEmptyString s = Data.List.and [isClear i j s | i <- [0..18], j <- [0..18]]

{-# INLINE inBounds #-}
inBounds (i, j) = 0 <= i && i < boardSize && 0 <= j && j < boardSize

{-# INLINE allAdj #-}
allAdj i j = filter inBounds [(i+1,j), (i,j+1), (i-1,j), (i,j-1)]

{-# INLINE seNeighWeak #-}
seNeighWeak i j = filter inBounds [(i-1,j+1), (i+1,j), (i+1,j+1), (i,j+1)]

{-# INLINE allAdjWeak #-}    
allAdjWeak i j = filter inBounds [(i+1,j),   (i,j+1),   (i-1,j),   (i,j-1),
                                  (i+1,j+1), (i-1,j+1), (i-1,j+1), (i-1,j-1)]

liberties stringMap board forBlack =
  countTrue [isClear i j board && someAdjOn i j stringMap | i <- [0..18], j <- [0..18]]
    where someAdjOn i j stringMap = or [isOn i' j' stringMap | (i', j') <- allAdj i j]
          countTrue xs = length [x | x <- xs, x]

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

-- User Interface

decodeMove :: String -> Maybe (Int, Int)
decodeMove str =
    if str == "pass" then Nothing else
    let (a,b) = Prelude.span (/=',') str in
    Just (read a, read (Prelude.tail b))

diagnose board forBlack i j =
    let stringMap = identifyString board forBlack i j in
    let l = liberties stringMap board forBlack in
    let n = length (findAllStrings board) in
    do putStrLn $ unlines $ lines (displayBoard board :: String)
                            `beside` lines (displayBoard stringMap)
       putStrLn $ "String has " ++ show l ++ " liberties"
       putStrLn $ "The board has " ++ show n ++ " strings"

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


-- * Parsing of boards for testing purposes.

parseChar '#' = Just True
parseChar 'O' = Just False
parseChar '.' = Nothing

bits (Just True) = 0x02
bits (Just False) = 0x01
bits Nothing = 0x00

-- Note this transposes the x and y axes--not desirable.
parseBoard :: String -> GameBoard
parseBoard str =
  let items = Data.List.concat [assert19 (map parseChar (filter (/=' ') l)) | l <- lines str] in
  let bitses = stride 4 (map bits items) in
  fromList (map makeByte bitses)

assert19 xs = if length xs == 19 then xs else error ("not 19 chars:" ++ show xs)

makeByte [x0,x1,x2,x3] = x3 `shiftL` 6 .|.
                         x2 `shiftL` 4 .|.
                         x1 `shiftL` 2 .|.
                         x0 `shiftL` 0
makeByte [x1,x2,x3] = makeByte [x3,x2,x1,0]
makeByte [x2,x3] = makeByte [x3,x2,0,0]
makeByte [x3] = makeByte [x3,0,0,0]

stride n xs = strideLoop n n xs
  where strideLoop n k [] = [[]]
        strideLoop n 0 xs = [] : strideLoop n n xs
        strideLoop n k (x:xs) = let (ys:yss) = strideLoop n (k-1) xs in
                                    (x:ys):yss


-- Bug: This ignores the groupMap. Need to flood just to the items in the groupMap
eyesOfGroup board groupMap isBlack =
    let desired = if isBlack then blackHaNib else whiteHaNib in
    filter (/= Nothing) $
        do i <- [0..18]
           j <- [0..18]
           if valueAt i j board /= desired then
             debug ("found seed at " ++ show (i,j)) $ 
             [flood board (/= desired) i j]
           else
             []

example1 = parseBoard
    "...................\n...................\n ..##...............\n ..#.#..............\n ..O##..............\n ..OOO..............\n .....O.............\n .....O.............\n ...................\n ...................\n ...................\n ...................\n ...................\n ...................\n ...................\n ...........#O......\n ..........#.#O.....\n ...........#O......\n ..................."

debugOn = False

debug x y = if debugOn then trace x y else y