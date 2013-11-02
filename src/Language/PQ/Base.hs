-- |Base.hs
--
-- Base combinators and implementation for the PQ.
--
-- Copyright (C) 2013 Serguey Zefirov.

{-# LANGUAGE TypeOperators, TypeFamilies, GADTs, FlexibleInstances, FlexibleContexts #-}
{-# LANGUAGE TemplateHaskell, UndecidableInstances, PatternGuards, StandaloneDeriving #-}
{-# LANGUAGE MultiParamTypeClasses, FunctionalDependencies #-}

module Language.PQ.Base
	( module Language.PQ.Base
	) where

import Control.Monad
import Control.Monad.State

import Data.Bits
import Data.Int
import Data.List (nub, intersect, isPrefixOf)
import qualified Data.Map as Map
import qualified Data.Set as Set
import Data.Word
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
	reifyNat ~(S n) = 1 + reifyNat n

-------------------------------------------------------------------------------
-- Bit-vactor representation for values.

class Nat (BitReprSize a) => BitRepr a where
	type BitReprSize a

	safeValue :: a
	safeValue = decode 0

	encode :: a -> Integer
	decode :: Integer -> a

	typeSize :: a -> BitReprSize a
	typeSize a = error "typeSize!!!"

	reifySize :: a -> Int
	reifySize a = reifyNat $ typeSize a

instance BitRepr Bool where
	type BitReprSize Bool = S Z
	safeValue = False
	encode = fromIntegral . fromEnum
	decode = toEnum . fromIntegral . (.&. 1)

instance BitRepr () where
	type BitReprSize () = Z
	safeValue = ()
	encode = const 0
	decode = const ()

type Dbl a = Plus a a

instance BitRepr Word8 where
	type BitReprSize Word8 = Dbl (Dbl (Dbl (S Z)))
	encode = fromIntegral
	decode = fromIntegral

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
	|	ESlice	SizedExpr	Int
	|	ERead	ChanID
	|	EWild
	deriving (Eq, Ord, Show)

data BinOp = Plus | Minus | Mul | Div | Mod | And | Or | Xor | Equal | NEqual | LessThan | GreaterThan | LessEqual | GreaterEqual
	deriving (Eq, Ord, Show)

data QE a where
	QE :: BitRepr a => SizedExpr -> QE a

qeValueSize :: BitRepr a => QE a -> Int
qeValueSize qe = reifySize (qeValue qe)
	where
		qeValue :: QE a -> a
		qeValue = error "qeValue!"

pqMkQE :: BitRepr a => Expr -> QE a
pqMkQE e = let r = QE (SE (qeValueSize r) e) in r

infixl 7 ./
infixl 7 .%
infixl 7 .*
infixl 6 .+
infixl 6 .-
class Arith a where
	(.+), (.-), (.*), (./), (.%) :: a -> a -> a

constant :: BitRepr a => a -> QE a
constant a = pqMkQE $ EConst (encode a)

mkBin :: (BitRepr a, BitRepr b) => BinOp -> QE a -> QE a -> QE b
mkBin op (QE a) (QE b) = pqMkQE $ EBin op a b

instance (BitRepr a, Arith a) => Arith (QE a) where
	(.+) = mkBin Plus
	(.-) = mkBin Minus
	(.*) = mkBin Mul
	(./) = mkBin Div
	(.%) = mkBin Mod

instance Arith Word8 where
	(.+) = (+)
	(.-) = (-)
	(.*) = (*)
	(./) = div
	(.%) = mod

class Equal a where
	type EqResult a
	(.==), (./=) :: a -> a -> EqResult a

instance (BitRepr a, Equal a) => Equal (QE a) where
	type EqResult (QE a) = QE Bool
	(.==) = mkBin Equal
	(./=) = mkBin NEqual

infixl 7 .&
infixl 5 .|, .^
class BitOp a where
	(.&), (.|), (.^) :: a -> a -> a

instance (BitRepr a, BitOp a) => BitOp (QE a) where
	(.&) = mkBin And
	(.|) = mkBin Or
	(.^) = mkBin Xor

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
	|	AFail	SizedExpr
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

deriving instance Show (Process ins outs)

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

_newTemp :: QE a -> ActionM (QE a)
_newTemp (QE e) = do
	i <- unique
	return $ QE $ SE (seSize e) (EVar (VarID Nothing [i]))

type family StringList ios
type instance StringList Nil = Nil
type instance StringList (a :. as) = String :. StringList as

class NamesList a where toNamesList :: a -> [String]
instance NamesList Nil where toNamesList Nil = []
instance NamesList as => NamesList (String :. as) where toNamesList (n :. ns) = n : toNamesList ns

class NamesList (StringList ins) => IOChans ins where
	inventChans :: StringList ins -> ins

instance IOChans Nil where
	inventChans Nil = Nil

instance (BitRepr a, IOChans ins) => IOChans (RChan a :. ins) where
	inventChans (n :. ns) = r :. inventChans ns
		where
			r = RChan (ChanID size defaultClock n)
			value :: RChan a -> a
			value = error "value!"

			size = reifySize (value r)

instance (BitRepr a, IOChans outs) => IOChans (WChan a :. outs) where
	inventChans (n :. ns) = r :. inventChans ns
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

process :: (IOChans (INS ins), IOChans (OUTS outs)) => String -> StringList (INS ins) -> StringList (OUTS outs) -> (INS ins -> OUTS outs -> ActionM ()) -> Process ins outs
process name insNames outsNames body = Process $ flip execState (startProc name) $ do
	let insNamesList = toNamesList insNames
	    outsNamesList = toNamesList outsNames
	when (not $ null $ intersect insNamesList outsNamesList) $ error "inputs and outputs intersect."
	when (length (nub insNamesList) /= length insNamesList) $ error "duplicate inputs names"
	when (length (nub outsNamesList) /= length outsNamesList) $ error "duplicate outputs names"
	body (inventChans insNames) (inventChans outsNames)

select :: BitRepr a => QE Bool -> QE a -> QE a -> QE a
select (QE c) tqe@(QE t) (QE f) = QE (SE (qeValueSize tqe) $ ESel c t f)

matchStat :: QE e -> [(QE a, ActionM ())] -> ActionM ()
matchStat e [] = error "matchStat on empty match list."
matchStat x@(QE e) matches = do
	t <- _newTemp x
	(t $= x) &&& (foldr1 (|||) $ map (matchAssigns t) matches)
	where
		matchAssigns (QE e) (QE match, comp) = do
			(c,assigns) <- genCond e match
			assigns &&& assert (QE c) &&& comp
		genCond :: SizedExpr -> SizedExpr -> ActionM (SizedExpr, ActionM ())
		genCond _ (SE _ EWild) = return (eTrue, _addAction ANop)
		genCond e v@(SE _ (EVar vid)) = do
			return (eTrue, _addAction $ AAssign v e)
		genCond e c@(SE _ (EConst _)) = do
			return (SE 1 $ EBin Equal e c, _addAction $ ANop)
		genCond e c@(SE _ (ECat es)) = do
			let subIndices = tail $ scanr (+) 0 $ map seSize es
			(conds, assigns) <- liftM unzip $ forM (zip subIndices es) $ \(ofs, se) ->
				genCond (SE (seSize se) (ESlice e ofs)) se
			return (foldl1 (\a b -> SE 1 $ EBin And a b) conds, foldl1 (&&&) assigns)

($=) :: QE a -> QE a -> ActionM ()
QE v $= QE e = case v of
	SE _ (EVar _) -> _addAction $ AAssign v e
	_ -> error $ "assignment into non-var."

def :: BitRepr a => String -> ActionM (QE a)
def name = do
	n <- unique
	let r = QE (SE (qeValueSize r) (EVar (VarID (Just name) [n])))
	return r
	
infixl 2 &&&
infixl 1 |||
infix 3 $=
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

writeC :: WChan a -> QE a -> ActionM ()
writeC (WChan chanID) (QE e) = _addAction $ AWrite chanID e

readC :: BitRepr a => RChan a -> QE a
readC (RChan cid) = pqMkQE $ ERead cid

pqTrue, pqFalse :: QE Bool
eFalse, eTrue :: SizedExpr
eFalse = SE 1 $ EConst 0
eTrue = SE 1 $ EConst 1
pqTrue = QE eTrue
pqFalse = QE eFalse

on :: QE Bool -> ActionM () -> ActionM ()
on (QE e) act = do
	before <- liftM procActions get
	modify $ \p -> p { procActions = [] }
	act
	after <- liftM procActions get
	modify $ \p -> p { procActions = before }
	_addAction $ AIf e after [ANop]

assert :: QE Bool -> ActionM ()
assert (QE cond) = _addAction $ AFail cond

loop :: ActionM () -> ActionM ()
loop actions = do
	before <- liftM procActions get
	modify $ \p -> p { procActions = [] }
	actions
	after <- liftM procActions get
	modify $ \p -> p { procActions = ALoop after : before }

__ :: BitRepr a => QE a
__ = pqMkQE EWild

class BitRepr b => Tuple a b | a -> b, b -> a where
	pqTup :: a -> QE b

(-->) :: QE a -> r -> (QE a, r)
qe --> r = (qe, r)

$(liftM concat $ forM [2..4] $ \n -> let
		names = map (mkName . ("a" ++) . show) [1..n]
		tupleTy = foldl AppT (TupleT n) $ map VarT names
		qeTupleTy = foldl AppT (TupleT n) $ map ((ConT ''QE `AppT`) . VarT) names
		bitReprSizeFT ty = ConT ''BitReprSize `AppT` ty
		bitReprs = map (\n -> ClassP ''BitRepr [VarT n]) names
		plusFT a b = ConT ''Plus `AppT` a `AppT` b
		sizeTE = foldl1 plusFT (map (bitReprSizeFT . VarT) names)
		bitReprI = InstanceD (ClassP ''Nat [sizeTE] : bitReprs) (ConT ''BitRepr `AppT` tupleTy)
			[TySynInstD ''BitReprSize [tupleTy] sizeTE]
		tupleI = InstanceD (ClassP ''BitRepr [tupleTy] : bitReprs) (ConT ''Tuple `AppT` qeTupleTy `AppT` tupleTy) [pqTupD]
		sizedExprE size e = ConE 'SE `AppE` size `AppE` e
		seSizeE se = VarE 'seSize `AppE` se
		pqTupD = FunD 'pqTup
			[Clause
				[TupP $ map (\n -> ConP 'QE [VarP n]) names]
				(NormalB (ConE 'QE `AppE` (sizedExprE (VarE 'sum `AppE` ListE (map (seSizeE . VarE) names)) (ConE 'ECat `AppE` ListE (map (\n -> VarE n) names))))) []]
		tupleNF =
			[ SigD fName (ForallT (map PlainTV names) (ClassP ''BitRepr [tupleTy] : bitReprs) $ ArrowT `AppT` qeTupleTy `AppT` (ConT ''QE `AppT` tupleTy))
			, FunD fName
				[Clause [] (NormalB $ VarE 'pqTup) []]
			]
			where
				fName = mkName $ "pqTup"++show n
	in return $ concat [[bitReprI, tupleI], tupleNF]
 )

pqDefs :: Q [Dec] -> Q [Dec]
pqDefs qdecs = do
	decs <- qdecs
	let r = decs ++ generatedDecs decs
--	runIO $ print $ ppr r
	return r
	where
		generatedDecs = concatMap genDecs
		genDecs (DataD cxt tyN varBinds conses _)
			| not (null cxt) = error "non-empty context of data declaration."
			| Nothing <- convertedVars = error "only plain type variables are supported."
			| Just names <- pureEnum = case vars of
				[] -> enumBitRepr names : concat (zipWith enumExprs [0..] names)
				_ -> phantomsArentSupported
			| otherwise = error "only enums are supported right now."
			where
				phantomsArentSupported = error "Phantom parameters are not supported."
				convertedVars = forM varBinds $ \vb -> case vb of
					PlainTV v -> return v
					_ -> Nothing
				Just vars = convertedVars
				pureEnum = forM conses $ \c -> case c of
					NormalC n [] -> Just n
					_ -> Nothing
				bitReprT ty = ConT ''BitRepr `AppT` ty
				dataTy = foldl AppT (ConT tyN) $ map VarT vars
				qeTy ty = ConT ''QE `AppT` ty
				toPeano 0 = ConT ''Z
				toPeano n = ConT ''S `AppT` toPeano (n-1)
				enumEncodeDecode names =
					[ FunD 'encode $ zipWith (\i n -> enc i n) [0..] names
					, FunD 'decode $ [Clause [VarP x] (NormalB decodeCase) []]
					]
					where
						decodeCase = CaseE (VarE 'mod `AppE` VarE x `AppE` LitE (IntegerL maxI)) (zipWith matches [0..] names)
						matches i n = Match (LitP $ IntegerL (index i)) (NormalB $ ConE n) []
						maxI = fromIntegral $ if bigEnum then namesLen else shiftL 1 namesLen
						namesLen = length names
						bigEnum = namesLen > 2
						x = mkName "x"
						index i
							| bigEnum = shiftL 1 i
							| otherwise = fromIntegral i
						enc i name = Clause [ConP name []] (NormalB $ LitE $ IntegerL $ index i) []
				enumBitRepr names = InstanceD [] (bitReprT dataTy)
					$ TySynInstD ''BitReprSize [dataTy] (toPeano $ if length names < 3 then length names -1 else length names)
					: enumEncodeDecode names
				enumExprs n conN = [SigD qeN (qeTy dataTy), FunD qeN [Clause [] (NormalB e) []]]
					where
						index = if length conses > 2 then shiftL 1 n else n
						e = VarE 'pqMkQE `AppE` (ConE 'EConst `AppE` LitE (IntegerL $ fromIntegral index))
						qeN = mkName $ "pq"++nameBase conN

