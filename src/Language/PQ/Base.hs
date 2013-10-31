-- |Base.hs
--
-- Base combinators and implementation for the PQ.
--
-- Copyright (C) 2013 Serguey Zefirov.

{-# LANGUAGE TypeOperators, TypeFamilies, GADTs, FlexibleInstances, FlexibleContexts #-}
{-# LANGUAGE TemplateHaskell, UndecidableInstances #-}

module Language.PQ.Base
	( module Language.PQ.Base
	) where

import Control.Monad
import Control.Monad.State

import Data.Bits
import Data.List (nub, intersect, isPrefixOf)
import qualified Data.Map as Map
import qualified Data.Set as Set
import Language.Haskell.TH
import qualified Language.Haskell.TH as TH

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
	|	EWild
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

mkQE :: BitRepr a => Expr -> QE a
mkQE e = let r = QE (SE (qeValueSize r) e) in r

-------------------------------------------------------------------------------
-- Defining the processes.

data ChanID = ChanID Int ClockInfo String
	deriving (Eq, Ord, Show)

data WChan a = WChan ChanID
	deriving (Eq, Ord, Show)

data RChan a = RChan ChanID
	deriving (Eq, Ord, Show)

data Action =
		ANop
	|	AWrite	ChanID		SizedExpr
	|	AAssign	SizedExpr	SizedExpr
	|	AGroup	GroupKind	Action	Action
	|	AIf	SizedExpr	[Action]	[Action]
	|	ALoop	[Action]
	deriving (Eq, Ord, Show)

data GroupKind = SeqActions | ParActions
	deriving (Eq, Ord, Show)

data Proc = Proc {
	  procName		:: String
	, procUnique		:: Int
	, procSubProcs		:: [Proc]
	, procActions		:: [Action]
	}
	deriving (Eq, Ord, Show)

_addAction :: Action -> ActionM ()
_addAction act = modify $ \p -> p { procActions = act : procActions p }

data Process ins outs where
	Process :: Proc -> Process ins outs

startProc :: String -> Proc
startProc name = Proc {
	  procName		= name
	, procUnique		= 0
	, procSubProcs		= []
	, procActions		= []
	}

type ActionM a = State Proc a

internal :: String -> a
internal s = error $ "internal error: "++s

unique :: ActionM Int
unique = do
	modify $ \p -> p { procUnique = 1 + procUnique p }
	liftM procUnique get

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

($=) :: QE a -> QE a -> ActionM ()
QE v $= QE e = case v of
	SE _ (EVar _) -> _addAction $ AAssign v e
	_ -> error $ "assignment into non-var."

def :: BitRepr a => String -> ActionM (QE a)
def name = do
	n <- unique
	let r = QE (SE (qeValueSize r) (EVar (VarID (Just name) [n])))
	return r

(&&&), (|||) :: ActionM () -> ActionM () -> ActionM ()
a1 &&& a2 = _group SeqActions a1 a2
a1 ||| a2 = _group ParActions a1 a2

_group :: GroupKind -> ActionM () -> ActionM () -> ActionM ()
_group kind a1 a2 = do
	as <- liftM procActions get
	let clear = modify $ \p -> p { procActions = [] }
	clear
	a1
	as1 <- liftM procActions get
	left <- case as1 of
		[a] -> return a
		_ -> error "left action is not singleton in group operator."
	clear
	a2
	as2 <- liftM procActions get
	right <- case as2 of
		[a] -> return a
		_ -> error "right action is not singleton in group operation."
	modify $ \p -> p { procActions = as }
	_addAction $ AGroup kind left right

write :: WChan a -> QE a -> ActionM ()
write (WChan chanID) (QE e) = _addAction $ AWrite chanID e

pqTrue, pqFalse :: QE Bool
pqTrue = QE (SE 1 $ EConst 1)
pqFalse = QE (SE 1 $ EConst 0)

on :: QE Bool -> ActionM () -> ActionM ()
on (QE e) act = do
	before <- liftM procActions get
	modify $ \p -> p { procActions = [] }
	act
	after <- liftM procActions get
	modify $ \p -> p { procActions = before }
	_addAction $ AIf e after [ANop]

loop :: ActionM () -> ActionM ()
loop actions = do
	before <- liftM procActions get
	modify $ \p -> p { procActions = [] }
	actions
	after <- liftM procActions get
	modify $ \p -> p { procActions = ALoop after : before }

__ :: BitRepr a => QE a
__ = mkQE EWild

class Tuple a where
	type TupleLifted a
	pqTup :: a -> TupleLifted a

--instance (BitRepr a, BitRepr b, BitRepr (a,b)) => Tuple (QE a,QE b) where
--	type TupleLifted (QE a,QE b) = QE (a,b)
--	pqTup (QE a,QE b) = QE $ SE (sum $ map seSize [a,b]) $ ECat [a,b]

(-->) :: Selectable r => QE a -> r -> (QE a, r)
qe --> r = (qe, r)

$(liftM concat $ forM [2..4] $ \n -> let
		names = map (mkName . ("a" ++) . show) [1..n]
		tupleTy = foldl AppT (TupleT n) $ map VarT names
		qeTupleTy = foldl AppT (TupleT n) $ map ((ConT ''QE `AppT`) . VarT) names
		bitReprSizeFT ty = ConT ''BitReprSize `AppT` ty
		bitReprSizes = map (\n -> ClassP ''BitRepr [VarT n]) names
		plusFT a b = ConT ''Plus `AppT` a `AppT` b
		bitReprI = InstanceD (ClassP ''Nat [bitReprSizeFT tupleTy] : bitReprSizes) (ConT ''BitRepr `AppT` tupleTy)
			[TySynInstD ''BitReprSize [tupleTy] (foldl1 plusFT (map VarT names))]
		tupleI = InstanceD (ClassP ''BitRepr [tupleTy] : bitReprSizes) (ConT ''Tuple `AppT` qeTupleTy) [pqTupD, tupleLiftedD]
		sizedExprE size e = ConE 'SE `AppE` size `AppE` e
		seSizeE se = VarE 'seSize `AppE` se
		tupleLiftedD = TySynInstD ''TupleLifted [qeTupleTy] (ConT ''QE `AppT` tupleTy)
		pqTupD = FunD 'pqTup
			[Clause
				[TupP $ map (\n -> ConP 'QE [VarP n]) names]
				(NormalB (ConE 'QE `AppE` (sizedExprE (VarE 'sum `AppE` ListE (map (seSizeE . VarE) names)) (ConE 'ECat `AppE` ListE (map (\n -> VarE n) names))))) []]
	in return [bitReprI, tupleI]
 )

pqDefs :: Q [Dec] -> Q [Dec]
pqDefs qdecs = do
	decs <- qdecs
	return decs
