-- |Library.hs
--
-- A set of handy combinators and types, like Prelude for Haskell.
--
-- Copyright (C) 2013 Serguey Zefirov

{-# LANGUAGE TypeOperators, TemplateHaskell, FlexibleContexts, TypeFamilies #-}

module Language.PQ.Library where

import Data.Int
import Data.Word

import Language.PQ.Base

-- |Simple "identity" process.
idP :: BitRepr a => Process (a :. Nil) (a :. Nil)
idP = process "id" ("in_data" :. Nil) ("out_data" :. Nil) $ \(input :. Nil) (output :. Nil) -> do
--	x <- def "x"
	loop $ do
--		x $= readC input &&& writeC output x
		writeC output (readC input)

-- |A buffer delay for one clock tick.
bufP :: BitRepr a => Process (a :. Nil) (a :. Nil)
bufP = process "buf" ("in_data" :. Nil) ("out_data" :. Nil) $ \(input :. Nil) (output :. Nil) -> do
	t <- def "temp"
	hasValue <- def "hasValue"
	hasValue $= pqFalse
	loop $ do
			on hasValue (writeC output t)
		&&& 	((t $= readC input &&& hasValue $= pqTrue) ||| hasValue $= pqFalse)

-- |Mapping process.
mapP :: (BitRepr a, BitRepr b) => (QE a -> QE b) -> Process (a :. Nil) (b :. Nil)
mapP f = process "map" ("in_data" :. Nil) ("out_data" :. Nil) $ \(input :. Nil) (output :. Nil) -> do
	x <- def "temp"
	loop $ do
		x $= readC input &&& writeC output (f x)

-- |Scanning combinator (see @scanl@ from Haskell Prelude).
-- The only possible way to scan input is left scan.
-- Reads input values, writes partial folds.
-- An example using scanl:
-- @> scanl (+) (-1) [1,2,3,4]@
-- @[-1,0,2,5,9]@
--
-- Given all that, it is easy to produce the running sum circuit:
--  runningSum = scanP "running_sum" (.+) (constant 0)
-- It will appear as "scan_running_sum" in the generated code.
scanP :: (BitRepr a, BitRepr b) => String -> (QE a -> QE b -> QE a) -> QE a -> Process (b :. Nil) (a :. Nil)
scanP suffix f a0 = process ("scan_"++suffix) ("in_data" :. Nil) ("out_data" :. Nil) $ \(input :. Nil) (output :. Nil) -> do
	t <- def "t"
	-- all assignments before @loop@ or other state changes or reads or something else
	-- are optimized into initial values of variables.
	t $= a0
	loop $ do
		-- write an output, read input and update partial folding value.
		writeC output t &&& t $= f t (readC input)

$(pqDefs [d|

 -- |Start-of-packet indicator.
 data SOP = NoSOP | SOP
	deriving (Eq, Ord, Show)

 -- |End-of-packet indicator.
 data EOP = NoEOP | EOP
	deriving (Eq, Ord, Show)

 |])

-- |Avalon streaming interface as a tuple.
-- Some data wrapped with start- and end-of-packet indicators.
-- Data can occur only between SOP and EOP.
-- Control signals ("ready" and "valid") are hidden in the channel logic.
type AS a = (SOP, EOP, a)

-- |The folding for Avalon streams.
-- The only possible way to fold such stream in hardware is the left fold.
foldP :: (BitRepr b, BitRepr (AS b), BitRepr a) => String -> (QE a -> QE b -> QE a) -> QE a -> Process (AS b :. Nil) (a :. Nil)
foldP suffix f a0 = process ("fold_"++suffix) ("in_data" :. Nil) ("out_data" :. Nil) $ \(input :. Nil) (output :. Nil) -> do
	t <- def "t"
	-- all assignments before @loop@ or other state changes or reads or something else
	-- are optimized into initial values of variables.
	t $= a0
	x <- def "x"
	loop $ do
		matchStat (readC input)
			[ pqTup (__ :: QE SOP, pqEOP, x) --> (writeC output (f t x) &&& (t $= a0))
			, pqTup (__, __, x) --> (t $= f t x)
			]

t =
	idP :: Process (Word8 :. Nil) (Word8 :. Nil)
	--foldP "qq" (.+) (constant 10 :: QE Word8)
g = putStrLn $ generate Verilog t
