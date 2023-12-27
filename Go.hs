{-# LANGUAGE MagicHash, BangPatterns, ScopedTypeVariables #-}
module Main where

import Control.Exception (catch)
import Control.Monad (when)
import Data.Vector hiding (span, tail, (++), zipWith, map, or, filter, length
                          , foldl', null, foldr1, replicate)
import qualified Data.Vector
import Data.Bits
import Data.Char
import Data.List
import Data.Maybe (catMaybes)
import Data.Word
import GHC.Types

import Debug.Trace

import System.Random

boardSize = 19

type GameBoard = Vector Word8
wordSize = 8
pointsPerWord = wordSize `div` 2

initialBoard :: GameBoard
initialBoard = generate (1 + boardSize * boardSize `div` pointsPerWord) (const 0)

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


header = "          1 1 1 1 1   \n0 2 4 6 8 0 2 4 6 8   \n"

displayBoardSized n board =
   unlines $ map (intersperse ' ') $ lines $ header ++ unlines [lineAt j | j <- [0..n-1]]
      where charFor 0 = '.'
            charFor 1 = 'O'
            charFor 2 = '#'
            charFor 3 = '%'
            charAt i j = charFor (valueAt i j board)
            lineAt :: Int -> String
            lineAt j = [charAt i j | i <- [0..n-1]]
                       ++ if even j then " " ++ padLeft 2 (show j) else "   "

padLeft n xs = replicate (n - length xs) ' ' ++ xs

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


-- | Returns a list of pairs (isBlack, stringMap) indicating a groupmap
-- at the given point and whether it is black or white.
identifyGroupAsColored board i j =
  case valueAt i j board of
    0x01 -> [(False, identifyGroup board False i j)]
    0x02 -> [(True, identifyGroup board True i j)]
    _ -> []

emptyStringMap = initialBoard

identifyString board forBlack i j =
  let desired = if forBlack then blackHaNib else whiteHaNib in
  let stringMap = emptyStringMap in
  -- Essentially a dfs with a stack for nodes to visit.
  let loop [] stringMap = stringMap
      loop ((i, j):todo) stringMap =
                  if isOn i j stringMap then {-drop it-} loop todo stringMap else
                  if valueAt i j board == desired then
                      let stringMap' = setOn i j stringMap in
                      loop (allAdj i j++todo) stringMap'
                  else loop todo stringMap
  in
    loop [(i, j)] stringMap

flood board okPred startI startJ =
  -- The algorithm is essentially a dfs with a stack for nodes to visit.
  let loop [] stringMap = if isEmptyString stringMap then Nothing else Just stringMap
      loop ((i, j) : todo) stringMap =
                  if pastEdge (i, j) then
                    debug ("flood from " ++ show (startI, startJ) ++
                           " hit edge, discarding")
                        Nothing
                  else
                  if isOn i j stringMap then {-drop it-} loop todo stringMap else
                  if okPred i j then
                      debug ("flood at " ++ show (i, j) ++ " ok, continuing") $
                      let stringMap' = setOn i j stringMap in
                      loop (allAdj i j++todo) stringMap'
                  else 
                      debug ("failed predicate at " ++ show(i,j) ++ " ignoring") $
                      loop todo stringMap
  in
    loop [(startI, startJ)] emptyStringMap

floodLimit board okPred limit startI startJ =
  -- The algorithm is essentially a dfs with a stack for nodes to visit.
  let loop [] count stringMap = if isEmptyString stringMap then Nothing else Just stringMap
      loop _ count _ | count > limit = Nothing
      loop ((i, j) : todo) count stringMap =
                  if pastEdge (i, j) then
                    debug ("flood from " ++ show (startI, startJ) ++
                           " hit edge, discarding")
                        Nothing
                  else
                  if isOn i j stringMap then {-drop it-} loop todo count stringMap else
                  if okPred i j then
                      debug ("flood at " ++ show (i, j) ++ " ok, continuing") $
                      let stringMap' = setOn i j stringMap in
                      loop (allAdj i j++todo) (count+1) stringMap'
                  else 
                      debug ("failed predicate at " ++ show(i,j) ++ " ignoring") $
                      loop todo count stringMap
  in
    loop [(startI, startJ)] 0 emptyStringMap

atEdge (i, j) = i == 0 || j == 0 || i == boardSize-1 || j == boardSize-1

pastEdge (i, j) = i < 0 || j < 0 || i > boardSize-1 || j > boardSize-1

identifyGroup board forBlack i j =
  let desired = if forBlack then blackHaNib else whiteHaNib in
  let stringMap = emptyStringMap in
  -- Essentially a dfs with a stack for nodes to visit.
  let loop [] stringMap = stringMap
      loop ((i, j):todo) stringMap =
                  if valueAt i j stringMap == 0x3 then loop todo stringMap else
                  if valueAt i j board == desired then
                      let stringMap' = setOn i j stringMap in
                      loop (allAdjWeak i j++todo) stringMap'
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

findAllGroups board =
    let boardPoints = [(i, j) | i <- [0..18], j <- [0..18]] in
    let (_, results) = 
          foldl' (\(masterMap, results) (i, j) -> 
                  if isClear i j masterMap then
                    case identifyGroupAsColored board i j of
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

{-# INLINE inBounds #-}
inBounds (i, j) = 0 <= i && i < boardSize && 0 <= j && j < boardSize

{-# INLINE allAdj #-}
allAdj i j = filter inBounds [(i+1,j), (i,j+1), (i-1,j), (i,j-1)]

{-# INLINE seNeighWeak #-}
seNeighWeak i j = filter inBounds [(i-1,j+1), (i+1,j), (i+1,j+1), (i,j+1), (i+1,j-1)]

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

--isDigit ch = '0' <= ord ch && ord ch <= '9'

readSafe [] = Nothing
readSafe [ch] | isDigit ch = return (fromDigit ch)
readSafe (d:str) | isDigit d =
    do num <- readSafe str
       return $ fromDigit d * 10 + num
readSafe _ = Nothing

fromDigit ch = ord ch - ord '0'

type Posn = (Int, Int)

data Color = Black | White

opp Black = White
opp White = Black

data Move = Pass | Next Posn | Forced Bool Posn

decodeMove :: String -> Maybe Move
decodeMove (' ':str) = decodeMove str
decodeMove str =
    if str == "pass" then Just Pass else
    if "black" `isPrefixOf` str then
      case decodeMove (Data.List.drop 5 str) of
         Nothing -> Nothing
         Just Pass -> Just Pass
         Just (Next p) -> Just (Forced True p)
         _ -> Nothing else
    if "white" `isPrefixOf` str then
      case decodeMove (Data.List.drop 5 str) of
         Nothing -> Nothing
         Just Pass -> Just Pass
         Just (Next p) -> Just (Forced False p)
         _ -> Nothing else
    let (i, etc) = Prelude.span isDigit str in
    let (junk, j) = Prelude.span (not . isDigit) etc in
    trace ("i: [" ++ i ++ "] j: [" ++ j ++ "]") $
    case (readSafe i, readSafe j) of
      (Just i', Just j') | inBounds (i', j') ->
          Just (Next (read i, read j))
      _ -> Nothing 

printState board forBlack (i, j) =
    let g = identifyGroupAsColored board i j in
    let stringMap = identifyStringAsColored board i j in
    let libs =
          case stringMap of [(_, stringMap')] -> 
                              liberties stringMap' board forBlack
                            _ -> 0
    in
    let groups = findAllGroups board in
    let livingGroups = [g | (g, eyes) <- eyedGroups board, length eyes > 1] in
    let livingGroupMap = foldr1 unionStringMaps livingGroups in
    do putStrLn $ unlines $ lines (displayBoard board :: String)
                              `beside` if not (null livingGroups) then
                                          lines (displayBoard livingGroupMap) else (repeat "")
       putStrLn $ "Latest string has " ++ show libs ++ " liberties"
       putStrLn $ "The board has " ++ show (length groups) ++ " groups with living groups: " ++
                  intercalate "," [show $ length eyes | (g, eyes) <- eyedGroups board]

eyedGroups board = 
    let groups = findAllGroups board in
    [(g, eyes) | g <- groups, let eyes = eyesOfGroup board g (groupColor board g), not (null eyes)]


-- Given the map of eyes.
-- scan the board
-- each time we hit a living 

-- If every stone is either living or dead:
-- The empty/dead neighbors of living stones belong to the same color as that stone; recurse!

finalScore board =
    let livingGroups = [g | (g, eyes) <- eyedGroups board, length eyes > 1] in
    let livingGroupMap = foldr1 unionStringMaps livingGroups in
    do j <- [0..18]
       i <- [0..18]
       if valueAt i j livingGroupMap == 0x03 then
         let livingColor = valueAt i j board in
         undefined
       else
         undefined

groupColor board group = 
  let boardIJs = [(i,j) | i <- [0..18], j <- [0..18]] in
  findAColor boardIJs
    where findAColor ((i,j):etc) =
            if valueAt i j board == blackHaNib then True else
            if valueAt i j board == whiteHaNib then False else
              findAColor etc

playLoop blackMove pass1 alterNot board lastMove = do
    printState board (not blackMove) lastMove
    putStr "> "
    move <- getLine
    if move == "quit" then putStrLn "Quitting" else 
      case decodeMove move of
        Nothing -> do putStrLn ("Not understood: " ++ move)
                      playLoop blackMove pass1 alterNot board lastMove
        Just Pass -> if pass1 then putStrLn "Done!"
                     else playLoop (not blackMove) True alterNot board (0,0)
        Just (Next (i, j)) -> do
          when (not (isClear i j board)) (do putStrLn "ILLEGAL MOVE";
                                             playLoop blackMove pass1 alterNot board lastMove)
          let tempBoard = (if blackMove then setBlack else setWhite) i j board
          let newBoard = killAdjacentDeadStrings tempBoard i j (not blackMove)
          playLoop (if alterNot then blackMove else not blackMove) False alterNot newBoard (i,j)
        Just (Forced player (i, j)) -> do
          let tempBoard = (if player then setBlack else setWhite) i j board
          let newBoard = killAdjacentDeadStrings tempBoard i j (not player)
          playLoop (if alterNot then blackMove else not blackMove) False alterNot newBoard (i,j)

play = 
   playLoop True False False initialBoard (0,0)

main = play

sandbox = 
   playLoop True False True initialBoard (0,0)

-- Got 154321 ops per second with -O3 and inlining.
benchmark 0 board = return board
benchmark count board =
  do x <- randomRIO (0,18)
     y <- randomRIO (0,18)
     b <- randomRIO (0,2::Int)
     let f = case b of 0 -> setWhite ; 1 -> setBlack ; 2 -> setClear
     let !newBoard = f x y board
     benchmark (count-1) newBoard

benchmarkMain = do
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

-- | Cut the list @xs@ into successive lists of @n@ elements each.
stride n xs = strideLoop n n xs
  where strideLoop n k [] = [[]]
        strideLoop n 0 xs = [] : strideLoop n n xs
        strideLoop n k (x:xs) = let (ys:yss) = strideLoop n (k-1) xs in
                                    (x:ys):yss

reasonableEyeSizeLimit = 20

-- TODO: This algorithm keeps exploring and discarding information
-- learned from different points. In fact, each flood we do teaches us
-- about all the points visited: whether or not they are part of an
-- eye. We should retain that information in the result map.
eyesOfGroup board groupMap isBlack =
    let desired = if isBlack then blackHaNib else whiteHaNib in
    Data.Maybe.catMaybes $
        do seedI <- [0..18]
           seedJ <- [0..18]
           if valueAt seedI seedJ board /= desired &&
              or [valueAt i j board == desired | (i, j) <- allAdj seedI seedJ] then
             debug ("found seed at " ++ show (seedI, seedJ)) $ 
             [floodLimit board (\i j -> not (isOn i j groupMap || pastEdge (i, j)))
                         reasonableEyeSizeLimit seedI seedJ]
           else
             []


example1 = parseBoard
    "...................\n...................\n ..##...............\n ..#.#..............\n ..O##..............\n ..OOO..............\n .....O.............\n .....O.............\n ...................\n ...................\n ...................\n ...................\n ...................\n ...................\n ...................\n ...........#O......\n ..........#.#O.....\n ...........#O......\n ..................."

example2 = parseBoard
         "...................\n...................\n...................\n.....###...........\n....##.#...........\n....#.#............\n....##.............\n...................\n...................\n...................\n...................\n...................\n...................\n...................\n...................\n...................\n...................\n...................\n..................."

debugOn = False

debug x y = if debugOn then trace x y else y


-- TODO:
-- Keep track of captures
-- determine living groups properly (check that each string borders two eyes of the same group)
-- identify eyes that touch boundary of board
-- count score at the end
-- prevent suicide moves
-- handle ko
-- more efficient string/group determination, using scanlines and union-find.
-- An eye cannot really be bigger than the minimal space in which the other
--   player can live. Minimal space to live is about 3x5:
--
--     xxxx
--     x x x
--      xxxx
--
-- We can stop flooding for an eye if we get to that point.



-- What's an eye?
-- An eye is a contiguous (strongly) set of dead/empty positions bounded by stones of a given color, or board-edges, which is NOT big enough for the other player to make two eyes.
-- what is big enough to make two eyes in?
-- something of at least width 3 by height 5?