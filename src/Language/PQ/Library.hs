-- |Library.hs
--
-- A set of handy combinators and types, like Prelude for Haskell.
--
-- Copyright (C) 2013 Serguey Zefirov

{-# LANGUAGE TypeOperators, TemplateHaskell #-}

module Language.PQ.Library where

import Language.PQ.Base

-- |Simple "identity" process.
idP :: Process (a :. Nil) (a :. Nil)
idP = process "id" ("input" :. Nil) ("output" :. Nil) $ \(input :. Nil) (output :. Nil) -> do
	x <- def "x"
	loop
		x $= read input &&& write output x

-- |A buffer delay for one clock tick.
bufP :: Process (a :. Nil) (a :. Nil)
bufP = process "buf" ("input" :. Nil) ("output" :. Nil) $ \(input :. Nil) (output :. Nil) -> do
	t <- def "temp"
	hasValue <- def "hasValue"
	loop
			when hasValue (write output t)
		&&& 	((t $= read input &&& hasValue $= pqTrue) ||| hasValue $= pqFalse)

-- |Mapping process.
mapP :: (QE a -> QE b) -> Process (a :. Nil) (b :. Nil)
mapP f = process "map" ("input" :. Nil) ("output" :. Nil) $ \(input :. Nil) (output :. Nil) -> do
	x <- def "temp"
	loop
		x $= read input &&& write output (f x)

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
scanP :: String -> (QE a -> QE b -> QE a) -> QE a -> Process (b :. Nil) (a :. Nil)
scanP suffix f a0 = process ("scan_"++suffix) ("input" :. Nil) ("output" :. Nil) $ \(input :. Nil) (output :. Nil) -> do
	t <- def "t"
	-- all assignments before @loop@ or other state changes or reads or something else
	-- are optimized into initial values of variables.
	t $= a0
	loop
		-- write an output, read input and update partial folding value.
		write output t &&& t $= f t (read input)

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
foldP :: String -> (QE a -> QE b -> QE a) -> QE a -> Process (AS b :. Nil) (AS a :. Nil)
foldP suffix f a0 = process ("fold_"++suffix) ("input" :. Nil) ("output" :. Nil) $ \(input :. Nil) (output :. Nil) -> do
	t <- def "t"
	-- all assignments before @loop@ or other state changes or reads or something else
	-- are optimized into initial values of variables.
	t $= a0
	x <- def "x"
	loop
		match (read input)
			[ pqTup (__, pqEOP, x) --> (write output (f t x) &&& t $= a0)
			, pqTup (__, __, x) --> (t $= f t x)
			]
