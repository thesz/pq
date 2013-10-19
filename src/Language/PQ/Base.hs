-- |Base.hs
--
-- Base combinators and implementation for the PQ.
--
-- Copyright (C) 2013 Serguey Zefirov.

{-# LANGUAGE TypeOperators, TypeFamilies #-}

module Language.PQ.Base
	( module Language.PQ.Base
	) where

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
	|	ERead	RChan
	deriving (Eq, Ord, Show)

data BinOp = Plus | Minus | Mul | Div | Mod | And | Or | Xor
	deriving (Eq, Ord, Show)

-------------------------------------------------------------------------------
-- Defining the processes.

data WChan = WChan ClockInfo String
	deriving (Eq, Ord, Show)

data RChan = RChan ClockInfo String
	deriving (Eq, Ord, Show)

data State = State {
	-- |Served as documentation naming one bit flag variable for this state.
	  stateName		:: Maybe String
	-- |Unique index - to make sure everything is unique and don't clash.
	, stateIndex		:: Int
	-- |List of state successors - most common case is only one state is next and less common for several states with conditions.
	, stateSuccessors	:: Either Int [(Int, SizedExpr)]
	}
	deriving (Eq, Ord, Show)

data Proc = Proc {
	  procName		:: String
	, procSubProcs		:: [Proc]
	, procStates		:: [State]
	}
	deriving (Eq, Ord, Show)
