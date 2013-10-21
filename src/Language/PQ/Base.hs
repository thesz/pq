-- |Base.hs
--
-- Base combinators and implementation for the PQ.
--
-- Copyright (C) 2013 Serguey Zefirov.

{-# LANGUAGE TypeOperators, TypeFamilies, GADTs, FlexibleInstances, FlexibleContexts #-}

module Language.PQ.Base
	( module Language.PQ.Base
	) where

import Control.Monad
import Control.Monad.State

import Data.Bits
import Data.List (nub, intersect, isPrefixOf)
import qualified Data.Map as Map
import qualified Data.Set as Set

-------------------------------------------------------------------------------
-- HList stuff.

data Nil = Nil
	deriving (Eq, Ord, Show)
data a :. b = a :. b
	deriving (Eq, Ord, Show)

-------------------------------------------------------------------------------
-- Type-level arithmetic.

data Z = Z
	deriving (Eq, Ord, Show)
data S n = S n
	deriving (Eq, Ord, Show)

type family Plus a b
type instance Plus Z a = a
type instance Plus (S a) b = S (Plus a b)

type family Max a b
type instance Max Z Z = Z
type instance Max (S a) Z = S a
type instance Max Z (S b) = S b
type instance Max (S a) (S b) = S (Max a b)

class Nat n where
	reifyNat :: n -> Int

instance Nat Z where
	reifyNat = const 0

instance Nat n => Nat (S n) where
	reifyNat (S n) = 1 + reifyNat n

-------------------------------------------------------------------------------
-- Bit-vactor representation for values.

class Nat (BitReprSize a) => BitRepr a where
	type BitReprSize a

	safeValue :: a
	safeValue = decode 0

	encode :: a -> Integer
	decode :: Integer -> a

	typeSize :: a -> BitReprSize a
	typeSize = const (error "typeSize!!!")

	reifySize :: a -> Int
	reifySize = reifyNat . typeSize

instance BitRepr Bool where
	type BitReprSize Bool = S Z
	safeValue = False
	encode = fromIntegral . fromEnum
	decode = toEnum . fromIntegral . (.&. 1)

-------------------------------------------------------------------------------
-- Clock information.

-- |Reset information for code generation.
data ResetInfo = ResetInfo {
	  resetName		:: String
	, resetHighActive	:: Bool
	, resetAsynchronous	:: Bool
	}
	deriving (Eq, Ord, Show)

-- |Clock information - for code generation and computations.
data ClockInfo = ClockInfo {
	  clockName		:: String
	, clockFrequency	:: Rational
	, clockFrontEdge	:: Bool
	, clockReset		:: ResetInfo
	}
	deriving (Eq, Ord, Show)

defaultReset :: ResetInfo
defaultReset = ResetInfo {
	  resetName		= "default_reset"
	, resetHighActive	= False
	, resetAsynchronous	= True
	}

defaultClock :: ClockInfo
defaultClock = ClockInfo {
	  clockName		= "default_clock"
	, clockFrequency	= 100000000
	, clockFrontEdge	= True
	, clockReset		= defaultReset
	}

-------------------------------------------------------------------------------
-- Expressions.

data SizedExpr = SE { seSize :: Int, seExpr :: Expr }
	deriving (Eq, Ord, Show)

data VarID = VarID (Maybe String) [Int]
	deriving (Eq, Ord, Show)

data Expr =
		EConst	Integer
	|	EVar	VarID
	|	EBin	BinOp		SizedExpr	SizedExpr
	|	ESel	SizedExpr	SizedExpr	SizedExpr
	|	ECat	[SizedExpr]
	|	ERead	ChanID
	deriving (Eq, Ord, Show)

data BinOp = Plus | Minus | Mul | Div | Mod | And | Or | Xor | Equal | LessThan | GreaterThan | LessEqual | GreaterEqual
	deriving (Eq, Ord, Show)

data QE a where
	QE :: BitRepr a => SizedExpr -> QE a

qeValueSize :: BitRepr a => QE a -> Int
qeValueSize qe = reifySize (qeValue qe)
	where
		qeValue :: QE a -> a
		qeValue = error "qeValue!"

-------------------------------------------------------------------------------
-- Defining the processes.

data ChanID = ChanID Int ClockInfo String
	deriving (Eq, Ord, Show)

data WChan a = WChan ChanID
	deriving (Eq, Ord, Show)

data RChan a = RChan ChanID
	deriving (Eq, Ord, Show)

data ExecPoint = ExecPoint {
	-- |Served as documentation naming one bit flag variable for this state.
	  epName		:: Maybe String
	-- |Unique index - to make sure everything is unique and don't clash.
	-- This is real identity of the execution point.
	, epIndex		:: Int
	-- |List of state successors - most common case is only one state is next and less common for several states with conditions.
	, epSuccessors	:: Either Int [(Int, SizedExpr)]
	-- |List of actions done at this point.
	, epActions		:: [Action]
	}
	deriving (Eq, Ord, Show)

data Action =
		AWrite	ChanID		SizedExpr
	|	AAssign	SizedExpr	SizedExpr
	deriving (Eq, Ord, Show)

data Proc = Proc {
	  procName		:: String
	, procUnique		:: Int
	, procSubProcs		:: [Proc]
	, procExecPoints	:: [ExecPoint]
	}
	deriving (Eq, Ord, Show)

data Process ins outs where
	Process :: Proc -> Process ins outs

startProc :: String -> Proc
startProc name = Proc {
	  procName		= name
	, procUnique		= 0
	, procSubProcs		= []
	, procExecPoints	= []
	}

type ActionM a = State Proc a

internal :: String -> a
internal s = error $ "internal error: "++s

class IOChans ins where
	inventChans :: [String] -> ins

instance IOChans Nil where
	inventChans [] = Nil

instance (BitRepr a, IOChans ins) => IOChans (RChan a :. ins) where
	inventChans (n : ns) = r :. inventChans ns
		where
			r = RChan (ChanID size defaultClock n)
			value :: RChan a -> a
			value = error "value!"

			size = reifySize (value r)

instance (BitRepr a, IOChans outs) => IOChans (WChan a :. outs) where
	inventChans (n : ns) = r :. inventChans ns
		where
			r = WChan (ChanID size defaultClock n)
			value :: WChan a -> a
			value = error "value!"

			size = reifySize (value r)

class Selectable e where
	selectResult :: QE Bool -> e -> e -> e

instance BitRepr t => Selectable (QE t) where
	selectResult c x y = select c x y

-------------------------------------------------------------------------------
-- Combinators visible to users.

type family INS ins
type instance INS Nil = Nil
type instance INS (i :. is) = RChan i :. INS is

type family OUTS ins
type instance OUTS Nil = Nil
type instance OUTS (i :. is) = WChan i :. OUTS is

process :: (IOChans (INS ins), IOChans (OUTS outs)) => String -> [String] -> [String] -> (INS ins -> OUTS outs -> ActionM ()) -> Process ins outs
process name insNames outsNames body = Process $ flip execState (startProc name) $ do
	when (not $ null $ intersect insNames outsNames) $ error "inputs and outputs intersect."
	when (length (nub insNames) /= length insNames) $ error "duplicate inputs names"
	when (length (nub outsNames) /= length outsNames) $ error "duplicate outputs names"
	body (inventChans insNames) (inventChans outsNames)

select :: BitRepr a => QE Bool -> QE a -> QE a -> QE a
select (QE c) tqe@(QE t) (QE f) = QE (SE (qeValueSize tqe) $ ESel c t f)

match :: Selectable r => QE e -> [(QE a, r)] -> r
match e matches = error "match!!!"
