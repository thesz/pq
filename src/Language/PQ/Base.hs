-- |Base.hs
--
-- Base combinators and implementation for the PQ.
--
-- Copyright (C) 2013 Serguey Zefirov.

{-# LANGUAGE TypeOperators, TypeFamilies, GADTs, FlexibleInstances #-}

module Language.PQ.Base
	( module Language.PQ.Base
	) where

import Control.Monad
import Control.Monad.State

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

-------------------------------------------------------------------------------
-- Bit-vactor representation for values.

-- class BitRepr 

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
	|	EBin	BinOp	SizedExpr	SizedExpr
	|	ECat	[SizedExpr]
	|	ERead	ChanID
	deriving (Eq, Ord, Show)

data BinOp = Plus | Minus | Mul | Div | Mod | And | Or | Xor
	deriving (Eq, Ord, Show)

-------------------------------------------------------------------------------
-- Defining the processes.

data ChanID = ChanID ClockInfo String
	deriving (Eq, Ord, Show)

data WChan a = WChan ChanID
	deriving (Eq, Ord, Show)

data RChan a = RChan ChanID
	deriving (Eq, Ord, Show)

data ExecPoint = ExecPoint {
	-- |Served as documentation naming one bit flag variable for this state.
	  epName		:: Maybe String
	-- |Unique index - to make sure everything is unique and don't clash.
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

instance IOChans ins => IOChans (RChan a :. ins) where
	inventChans (n : ns) = RChan (ChanID defaultClock n) :. inventChans ns

instance IOChans outs => IOChans (WChan a :. outs) where
	inventChans (n : ns) = WChan (ChanID defaultClock n) :. inventChans ns

-------------------------------------------------------------------------------
-- Combinators for users.

type family INS ins
type instance INS Nil = Nil
type instance INS (i :. is) = RChan i :. INS is

type family OUTS ins
type instance OUTS Nil = Nil
type instance OUTS (i :. is) = WChan i :. OUTS is

process :: String -> [String] -> [String] -> (INS ins -> OUTS outs -> ActionM ()) -> Process ins outs
process name insNames outsNames body = Process $ flip execState (startProc name) $ do
	when (not $ null $ intersect insNames outsNames) $ error "inputs and outputs intersect."
	when (length (nub insNames) /= length insNames) $ error "duplicate inputs names"
	when (length (nub outsNames) /= length outsNames) $ error "duplicate outputs names"
	body undefined undefined

