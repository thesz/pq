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
import Data.List (nub, nubBy, intersect, isPrefixOf, intersperse, intercalate)
import qualified Data.Map as Map
import Data.Maybe (catMaybes)
import qualified Data.Set as Set
import Data.Word
import Language.Haskell.TH
import qualified Language.Haskell.TH as TH
import Text.Printf

import Debug.Trace

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

data VarID = VarID [String] [Int]
	deriving (Eq, Ord, Show)

data Expr =
		EConst	Integer
	|	EVar	VarID
	|	EBin	BinOp		SizedExpr	SizedExpr
	|	EUn	UnOp		SizedExpr
	|	ESel	SizedExpr	SizedExpr	SizedExpr
	|	ECat	[SizedExpr]
	|	ESlice	SizedExpr	Int
	|	ERead	ChanID
	|	EWild
	deriving (Eq, Ord, Show)

data BinOp = Plus | Minus | Mul | Div | Mod | And | Or | Xor | Equal | NEqual | LessThan | GreaterThan | LessEqual | GreaterEqual
	deriving (Eq, Ord, Show)

data UnOp = Negate | Not
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

instance BitOp SizedExpr where
	 a .& b = SE 1 $ EBin And a b
	 a .| b = SE 1 $ EBin Or a b
	 a .^ b = SE 1 $ EBin Xor a b
-------------------------------------------------------------------------------
-- Defining the processes.

data ChanID = ChanID { cidSize :: Int, cidClockInfo :: ClockInfo, cidName :: [String] }
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

data SubProc = SubProc {
	  spProcess		:: Proc
	, spIns			:: [ChanID]
	, spOuts		:: [ChanID]
	}
	deriving (Eq, Ord, Show)

data Proc = Proc {
	  procName		:: String
	, procUnique		:: Int
	, procInputs		:: [ChanID]
	, procOutputs		:: [ChanID]
	, procSubProcs		:: [SubProc]
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
	, procInputs		= []
	, procOutputs		= []
	, procSubProcs		= []
	, procActions		= []
	}

type ActionM a = State Proc a

internal :: String -> a
internal s = error $ "internal error: "++s

class Unique m where
	unique :: m Int

instance Unique (State Proc) where
	unique = do
		modify $ \p -> p { procUnique = 1 + procUnique p }
		liftM procUnique get

newVarID :: (Monad m, Unique m) => [String] -> m VarID
newVarID names = do
	x <- unique
	return $ VarID names [x]

_newTemp :: QE a -> ActionM (QE a)
_newTemp (QE e) = do
	i <- unique
	return $ QE $ SE (seSize e) (EVar (VarID [] [i]))

type family StringList ios
type instance StringList Nil = Nil
type instance StringList (a :. as) = String :. StringList as

class NamesList a where toNamesList :: a -> [String]
instance NamesList Nil where toNamesList Nil = []
instance NamesList as => NamesList (String :. as) where toNamesList (n :. ns) = n : toNamesList ns

class NamesList (StringList cs) => IOChans cs where
	inventChans :: StringList cs -> cs
	chanList :: cs -> [ChanID]

instance IOChans Nil where
	inventChans Nil = Nil
	chanList _ = []

instance (BitRepr a, IOChans ins) => IOChans (RChan a :. ins) where
	inventChans (n :. ns) = r :. inventChans ns
		where
			r = RChan (ChanID size defaultClock [n])
			value :: RChan a -> a
			value = error "value!"

			size = reifySize (value r)
	chanList (RChan c :. cs) = c : chanList cs

instance (BitRepr a, IOChans outs) => IOChans (WChan a :. outs) where
	inventChans (n :. ns) = r :. inventChans ns
		where
			r = WChan (ChanID size defaultClock [n])
			value :: WChan a -> a
			value = error "value!"

			size = reifySize (value r)
	chanList (WChan c :. cs) = c : chanList cs

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
	let ins = inventChans insNames
	    outs = inventChans outsNames
	modify $ \p -> p
		{ procInputs = chanList ins
		, procOutputs = chanList outs
		}
	body ins outs
	modify $ \p -> p { procActions = reverse $ procActions p }

instantiate :: String -> Process ins outs -> ActionM (INS outs, OUTS ins)
instantiate instanceName process = error "instantiate!"

select :: BitRepr a => QE Bool -> QE a -> QE a -> QE a
select (QE c) tqe@(QE t) (QE f) = QE (SE (qeValueSize tqe) $ ESel c t f)

class Reclock c where reclockChan :: ClockInfo -> c -> ActionM ()
instance Reclock (WChan a) where reclockChan ci (WChan cid) = error "reclock wchan!"
instance Reclock (RChan a) where reclockChan ci (RChan cid) = error "reclock wchan!"

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
			return (foldl1 (.&) conds, foldl1 (&&&) assigns)

($=) :: QE a -> QE a -> ActionM ()
QE v $= QE e = case v of
	SE _ (EVar _) -> _addAction $ AAssign v e
	_ -> error $ "assignment into non-var."

def :: BitRepr a => String -> ActionM (QE a)
def name = do
	v <- newVarID [name]
	let r = QE (SE (qeValueSize r) (EVar v))
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
		sizeN i = mkName $ "size"++show i
		shiftN i = mkName $ "shift"++show i
		encodeTuple = FunD 'encode [Clause [TupP $ map VarP names] (NormalB encodeE) (sizes ++ shifts)]
			where
				encodeE = foldl1 (\a b -> InfixE (Just a) (VarE $ mkName ".|.") (Just b)) $
					zipWith (\a s -> VarE 'shiftL `AppE` (VarE 'encode `AppE` VarE a) `AppE` VarE (shiftN s))
						names [1..]
				sizes = zipWith (\a s -> ValD (VarP s) (NormalB $ VarE 'reifySize `AppE` VarE a) []) names (map sizeN [1..n])
				shifts = map shift [1..n]
				shift i
					| i >= n = ValD (VarP (shiftN i)) (NormalB $ LitE $ IntegerL 0) []
					| otherwise = ValD (VarP (shiftN i)) (NormalB $ InfixE (Just $ VarE $ sizeN (i+1)) (VarE $ mkName "+") (Just $ VarE (shiftN (i+1)))) []
		decodeTuple = FunD 'decode [Clause [VarP x] (NormalB decodeE) []]
			where
				x = mkName "x"
				decodeE = VarE 'undefined
		bitReprI = InstanceD (ClassP ''Nat [sizeTE] : bitReprs) (ConT ''BitRepr `AppT` tupleTy)
			$ TySynInstD ''BitReprSize [tupleTy] sizeTE
			: encodeTuple : decodeTuple : []
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

-------------------------------------------------------------------------------
-- Transforming process AST into AST for code generation.

data Language = Verilog | VHDL
	deriving (Eq, Ord, Show)

data ExecPoint = ExecPoint {
	  epLabel		:: VarID
	, epFirst		:: Bool
	, epSucceedVar		:: VarID
	, epControlFlow		:: ([(SizedExpr, VarID)], VarID)
	}
	deriving (Eq, Ord, Show)

data GenS = GS {
	  gsUnique		:: Int
	, gsLabelI		:: Int
	, gsLanguage		:: Language
	, gsDefaults		:: Map.Map VarID SizedExpr
	, gsPoints		:: [ExecPoint]
	, gsClock		:: ClockInfo
	, gsSeenProcesses	:: Map.Map Proc	String
	, gsLines		:: [String]
	, gsNest		:: String
	, gsDeclared		:: Set.Set VarID
	, gsAssignments		:: [(VarID, SizedExpr)]
	, gsRegAssignments	:: [(VarID, SizedExpr)]
	}
	deriving (Eq, Ord, Show)

startGenS :: Language -> GenS
startGenS l = GS {
	  gsUnique		= 0
	, gsLabelI		= 0
	, gsLanguage		= l
	, gsDefaults		= Map.empty
	, gsPoints		= []
	, gsClock		= internal "gsClock wasn't set."
	, gsSeenProcesses	= Map.empty
	, gsLines		= []
	, gsNest		= ""
	, gsDeclared		= Set.empty
	, gsAssignments		= []
	, gsRegAssignments	= []
	}

type GenM a = State GenS a

instance Unique (State GenS) where
	unique = do
		modify $ \gs -> gs { gsUnique = gsUnique gs + 1 }
		liftM gsUnique get

genLine :: String -> GenM ()
genLine s = do
	modify $ \gs -> gs {
		  gsLines = (if null s then "" else (gsNest gs ++ s)) : gsLines gs
		}

genNL :: GenM ()
genNL = modify $ \gs -> gs { gsLines = "" : gsLines gs }

genNest :: GenM a -> GenM a
genNest a = do
	old <- liftM gsNest get
	modify $ \gs -> gs { gsNest = "    "++gsNest gs }
	x <- a
	modify $ \gs -> gs { gsNest = old }
	return x

genLanguage :: GenM Language
genLanguage = liftM gsLanguage get

genComment :: String -> GenM ()
genComment c = do
	l <- genLanguage
	genLine $ case l of
		Verilog -> "// "++c
		VHDL -> "-- "++c

genChanName :: ChanID -> String
genChanName (ChanID _ _ ns) = intercalate "_" ns

genChanReady, genChanValid, genChanData :: ChanID -> VarID
genChanReady (ChanID _ _ names) = VarID (names ++ ["ready"]) []
genChanValid (ChanID _ _ names) = VarID (names ++ ["valid"]) []
genChanData (ChanID _ _ names) = VarID (names) []


genVarName :: VarID -> String
genVarName (VarID names indices) = intercalate "_" $ names ++ map show indices

genAddDeclared :: VarID -> GenM ()
genAddDeclared v = modify $ \gs -> gs { gsDeclared = Set.insert v $ gsDeclared gs }

genIsNotDeclared :: VarID -> GenM Bool
genIsNotDeclared v = liftM (not . Set.member v . gsDeclared) get

genHeader :: String -> Proc -> GenM ()
genHeader n process = do
	genNL
	genComment $ "header for module "++n++" of process "++procName process
	l <- genLanguage
	case l of
		Verilog -> do
			genLine $ "module "++n
			genNest $ do
				forM_ (zip ("(" : repeat ",") clocksResets) $ \(c,i) -> genLine $ c++" input "++replicate 14 ' '++i
				forM_ ios $ \(d,v) -> do { genLine $ ", "++d; genAddDeclared v}
				genLine ");"
			genNL
		VHDL -> error "header generation for VHDL."
	where
		clocks = getClocks process
		clockNames = nub $ map clockName clocks
		resetNames = nub $ map (resetName . clockReset) clocks
		clocksResets = clockNames ++ resetNames
		getClocks process = map (cidClockInfo) $ procInputs process ++ procOutputs process
		inChans = procInputs process
		outChans = procOutputs process
		ios = concatMap (genChan "input " "output") inChans ++ concatMap (genChan "output" "input ") outChans
		genChan dirTo dirFrom cid@(ChanID size _ name) =
			dataIO ++ [declare dirTo 1 genChanValid, declare dirFrom 1 genChanReady]
			where
				declare dir size f = (unwords [dir, sizeDecl, genVarName $ f cid], v)
					where
						v = f cid
						sizeDecl
							| size < 2 = replicate 12 ' '
							| otherwise = take 12 $ concat ["[", show (size-1),":0]"]++repeat ' '
				dataIO = if size < 1 then [] else [declare dirTo size $ \(ChanID _ _ names) -> VarID names []]


genFooter :: String -> GenM ()
genFooter n = do
	l <- genLanguage
	case l of
		VHDL -> genLine $ "end architecture implementation_arch;"
		Verilog -> genLine $ "endmodule"

genExecLabel :: Int -> VarID
genExecLabel i = VarID ["pq_label"] [i]

genNextLabel :: GenM VarID
genNextLabel = liftM (genExecLabel . (+1) . gsLabelI) get

genCurrentLabel :: GenM VarID
genCurrentLabel = liftM (genExecLabel . gsLabelI) get

genChangeLabel :: VarID -> VarID -> GenM ()
genChangeLabel origL toL = modify $ \gs -> gs {
	  gsPoints = map changeL $ gsPoints gs
	}
	where
		changeL (ExecPoint label succeed (condChanges, elseChange)) =
			ExecPoint label succeed (map condChange condChanges, change elseChange)
		condChange (e,l) = (e,change l)
		change l
			| l == origL = toL
			| otherwise = l

genNextLabelI :: GenM ()
genNextLabelI = modify $ \gs -> gs { gsLabelI = gsLabelI gs + 1 }


genActionsExecPoints :: [Action] -> GenM ()
genActionsExecPoints actions = do
	(registers, assignments, body) <- genGetRegisters actions
	mapM_ assignmentsFirst assignments
	mapM_ addConvert body
	modify $ \gs -> gs { gsPoints = reverse $ gsPoints gs }
	modify $ \gs -> gs { gsClock = actionsClock}
	assignLabelsRegs
	where
		referrers ep = liftM (concatMap refs . gsPoints) get
			where
				refs ep'
					| not (null $ fst $ epControlFlow ep') = internal $ "complete control flow is not supported."
					| snd (epControlFlow ep') == epLabel ep = [ep']
					| otherwise = []
		assignLabelsRegs = do
			eps <- liftM gsPoints get
			forM_ eps $ \ep -> do
				modify $ \gs -> gs { gsDefaults = Map.insert (epLabel ep) (if epFirst ep then eTrue else eFalse) $ gsDefaults gs }
				let logicEV v = SE 1 $ EVar v
				    succeed ep = logicEV (epLabel ep) .& logicEV (epSucceedVar ep)
				refs <- referrers ep
				modify $ \gs -> gs { gsRegAssignments = (epLabel, foldl1 (.|) $ map succeed refs) : gsRegAssignments gs }
		actionsClock = case nubBy (\a b -> cidClockInfo a == cidClockInfo b) $ concatMap actionClock actions of
			[] -> error $ "No channel operations detected, cannot determine what clock to use."
			[c] -> cidClockInfo c
			cs -> error $ "Port operations with different clocks: "++show cs
		actionClock (AWrite cid e) = cid : exprChans e
		actionClock (ALoop actions) = concatMap actionClock actions
		actionClock (AGroup _ a b) = concatMap actionClock [a,b]
		actionClock (AAssign a e) = exprChans e
		actionClock a = internal $ "actionClock: "++show a
		exprChans (SE _ e) = case e of
			ERead cid -> [cid]
			EBin _ a b -> exprChans a ++ exprChans b
			EUn _ a -> exprChans a
			EVar _ -> []
			EConst _ -> []
			e -> internal $ "exprChans "++show e
		exprValidReady f (SE _ e) = case e of
			ERead cid -> Just $ SE 1 $ EVar $ f cid
			EConst _ -> Nothing
			EVar _ -> Nothing
			EBin _ a b -> foldrs $ catMaybes [exprValidReady f a, exprValidReady f b]
			e -> internal $ "exprValidReady "++show e
			where
				foldrs [] = Nothing
				foldrs rs = Just $ foldl1 (.&) rs
		assignmentsFirst (AAssign (SE _ (EVar var)) expr) = do
			case expr of
				SE size (EConst c) -> modify $ \gs -> gs { gsDefaults = Map.insert var expr $ gsDefaults gs}
				_ -> internal $ "not a constant in assigning "++show var
		assignmentsFirst a = internal $ show a ++ " in assignmentsFirst."
		addConvert (ALoop actions) = convertToExecPoint (ALoop actions)
		addConvert action = do
			this <- genCurrentLabel
			next <- genNextLabel
			let execPoint = ExecPoint this (internal "no succeed var") ([], next)
			modify $ \gs -> gs { gsPoints = execPoint : gsPoints gs }
			succeed <- convertToExecPoint' this action
			onTopEP $ \ep -> ep {
				  epSucceedVar = succeed
				}
			genNextLabelI
			return ()
		-- top-level conversion function.
		convertToExecPoint (ALoop actions) = do
			begin <- genCurrentLabel
			mapM_ addConvert actions
			exit <- genCurrentLabel
			genChangeLabel exit begin
		convertToExecPoint a@(AGroup _ _ _) = do
			start <- genCurrentLabel
			convertToExecPoint' start a
			return ()
		convertToExecPoint a = internal $ "convertToExecPoint top "++show a++"!"

		onTopEP changeEP = modify $ \gs -> gs { gsPoints = case gsPoints gs of
				ep : eps -> changeEP ep : eps
				eps -> eps
			}

		addAssign var sizedExpr = do
			modify $ \gs -> gs { gsAssignments = (var, sizedExpr) : gsAssignments gs }
			
		succeedVar = newVarID ["pq","succeed"]

		-- conversion function of internals of exec point.
		convertToExecPoint' started (AGroup SeqActions a b) = do
			succeed' <- convertToExecPoint' started a
			convertToExecPoint' succeed' b
		convertToExecPoint' started (AGroup ParActions a b) = do
			succeedA <- convertToExecPoint' started a
			startedB <- succeedVar
			addAssign startedB (SE 1 $ EBin And (SE 1 $ EVar started) (SE 1 $ EUn Not $ (SE 1 $ EVar succeedA)))
			succeedB <- convertToExecPoint' startedB b
			succeedAny <- succeedVar
			addAssign succeedAny ((SE 1 $ EVar succeedA) .| (SE 1 $ EVar succeedB))
			return succeedAny
		convertToExecPoint' succeed (AAssign (SE _ (EVar v)) sizedE) = do
			let valid = exprValidReady genChanValid sizedE
			addAssign v sizedE
			succeed' <- case valid of
				Just e -> do
					succeed' <- succeedVar
					addAssign succeed' $ (SE 1 $ EVar succeed) .& e
					return succeed'
				Nothing -> return succeed
			return succeed'
		convertToExecPoint' succeed ANop = return succeed
		convertToExecPoint' succeed (AWrite chan expr) = do
			addAssign (genChanData chan) expr
			succeed' <- succeedVar
			let valid = exprValidReady genChanValid expr
			    withValid e = maybe e (e .&) valid
			addAssign succeed' $ (SE 1 $ EVar $ genChanReady chan) .& withValid (SE 1 $ EVar succeed)
			return succeed
		convertToExecPoint' succeed (AFail cond) = do
			v <- succeedVar
			addAssign v (SE 1 $ EBin And (SE 1 $ EVar succeed) cond)
			return succeed
		convertToExecPoint' succeed a = internal $ "conversion to exec point of "++show a

genDumpExecPoints :: GenM ()
genDumpExecPoints = do
	l <- genLanguage
	eps <- liftM gsPoints get
	asgns <- liftM gsAssignments get
	regs <- liftM
	genComment "Declarations."
	genNL
	forM_ eps $ declare l
	genNL
	genComment "State changing assignments as combinational logic."
	forM_ asgns $ assign l
	genNL
	genComment "All registers."
	forM_ 
	genNL
	return ()
	where
		assign Verilog (var, expr) = 
			genLine $ unwords ["assign",genVarName var, "=", vlogExpr expr]++";"
		assign VHDL (var, expr) =
			genLine $ unwords [genVarName var, "<=", vhdlExpr expr]++";"
		vhdlExpr e = internal $ "vhdl expr!"
		vlogExpr (SE size e) = case e of
			EConst c -> printf "%d'h%x" size c
			EVar v -> genVarName v
			EBin op a b -> bin $ case op of
				Plus -> "+"
				Minus -> "-"
				Mul -> "*"
				Div -> "/"
				Mod -> "%"
				And -> "&"
				Or -> "|"
				Xor -> "^"
				Equal -> "=="
				NEqual -> "!="
				LessThan -> "<"
				GreaterThan -> ">"
				LessEqual -> "<="
				GreaterEqual -> ">="
				where
					bin s = unwords [as, s, bs]
					as = vlogExpr a
					bs = vlogExpr b
			EUn op a -> (++vlogExpr a) $ case op of
				Negate -> "-"
				Not -> "~"
			ESel a b c -> unwords [vlogExpr a, "?", vlogExpr b, ":", vlogExpr c]
			ECat es -> concat ["{",intercalate ", " (map vlogExpr es), "}"];
			ESlice e ofs -> concat [vlogExpr e, "[",show (ofs+size-1),":", show ofs,"]"]
			ERead c -> genChanName c
			EWild -> ""
		declare lang ep = do
			regs <- liftM (map (\(v,se) -> (seSize se, v)) . gsRegAssignments) get
			forM_ regs $ declareAsgn True lang
			asgns <- liftM gsAssignments get
			forM_ (nub $ concatMap asgnDecls asgns) $ declareAsgn False lang
		declareAsgn reg Verilog (size, var) = do
			genIsNotDeclared var >>= flip when ((genLine $ unwords [if reg then "reg" else "wire", sizeDecl, genVarName var]++";") >> genAddDeclared var)
			where
				sizeDecl
					| size < 2 = ""
					| otherwise = concat ["[",show (size-1),":0]"]
		declareAsgn _ VHDL (size, var) = do
			genLine $ unwords ["signal",genVarName var,":",sizeDecl]++";"
			where
				sizeDecl
					| size < 2 = "bit"
					| otherwise = concat ["unsigned(", show (size-1)," downto 0)"]
		asgnDecls (var, e@(SE size _)) = [(size, var)] ++ exprDecls e
		exprDecls (SE size e) = case e of
			EConst	_ -> []
			EVar var -> [(size, var)]
			EBin _ a b -> exprDecls a ++ exprDecls b
			EUn _ a -> exprDecls a
			ESel a b c -> concatMap exprDecls [a,b,c]
			ECat es -> concatMap exprDecls es
			ESlice e _ -> exprDecls e
			ERead _ -> []
			EWild -> []

genProcess :: Proc -> GenM ()
genProcess process = do
	n <- liftM (Map.lookup process . gsSeenProcesses) get
	case n of
		Nothing -> do
			n <- inventName
			genHeader n process
			gen
			genFooter n
		Just _ -> return ()
	where
		inventName = do
			names <- liftM (Set.fromList . Map.elems . gsSeenProcesses) get
			let goodName = head $ filter (\n -> not $ Set.member n names) $ procName process
				: map (\i -> procName process ++"_"++show i) [1..]
			modify $ \gs -> gs { gsSeenProcesses = Map.insert process goodName $ gsSeenProcesses gs }
			return goodName
		gen = do
			genNL
			genComment $ "Instantiating sub processes."
			forM_ (procSubProcs process) $ \sp -> error "generating subprocesses is not yet done!"
			genNL
			genComment $ "The body."
			genInitDefs $ procActions process
			genActionsExecPoints $ procActions process
			genDumpExecPoints
			genComment $ "Process "++procName process

genGetRegisters :: [Action] -> GenM (Map.Map VarID Int, [Action], [Action])
genGetRegisters actions = return (registers, assigns, body)
	where
		(assigns, body) = span isAssign actions
		isAssign (AAssign _ _) = True
		isAssign _ = False
		registers = findRegisters body
		findRegisters actions = Map.unions $ map snd $ map findFirst actions
		findFirst :: Action -> (Map.Map VarID Int, Map.Map VarID Int)
		findFirst a = case a of
			ANop -> (Map.empty, Map.empty)
			AFail se -> (Map.empty, genSizedExprVars se)
			AWrite _ se -> (Map.empty, genSizedExprVars se)
			AAssign	v se -> (genSizedExprVars v, genSizedExprVars se)
			AGroup SeqActions a b -> (Map.union defA defB, Map.union usedA (Map.difference usedB defA))
				where
					(defA, usedA) = findFirst a
					(defB, usedB) = findFirst b
			AGroup ParActions a b -> (Map.intersection usedA usedB, Map.union usedA usedB)
				where
					(defA, usedA) = findFirst a
					(defB, usedB) = findFirst b
			AIf se as1 as2 -> (Map.empty, Map.unions [genSizedExprVars se, findRegisters as1, findRegisters as2])
			ALoop actions -> (Map.empty, findRegisters actions)

genInitDefs :: [Action] -> GenM ()
genInitDefs actions = do
	(registers, _, _) <- genGetRegisters actions
	modify $ \gs -> gs { gsDefaults = Map.map (\s -> SE s (EConst 0)) registers }


genUnionVars :: [Map.Map VarID Int] -> Map.Map VarID Int
genUnionVars varSets = foldr (Map.unionWithKey checkDups) Map.empty varSets
	where
		checkDups vid sz1 sz2
			| sz1 == sz2 = sz1
			| otherwise = error $ show vid++" has two different sizes "++show (sz1, sz2)

genExprVars :: Expr -> Map.Map VarID Int
genExprVars e = case e of
	EConst _ -> Map.empty
	EBin _ a b -> genUnionVars $ map genSizedExprVars [a,b]
	ESel c t e -> genUnionVars $ map genSizedExprVars [c,t,e]
	ECat ses -> genUnionVars $ map genSizedExprVars ses
	ESlice e _ -> genSizedExprVars e
	ERead _ -> Map.empty
	EWild -> Map.empty

genSizedExprVars :: SizedExpr -> Map.Map VarID Int
genSizedExprVars (SE size (EVar varID)) = Map.singleton varID size
genSizedExprVars se = genExprVars $ seExpr se

genGetActionsVars :: [Action] -> Map.Map VarID Int
genGetActionsVars actions = genUnionVars $ map actionVars actions
	where
		actionVars act = case act of
			ANop -> Map.empty
			AFail se -> genSizedExprVars  se
			AWrite	_ e -> genSizedExprVars e
			AAssign a b -> genUnionVars $ map genSizedExprVars [a,b]
			AGroup _ a b -> genUnionVars $ map actionVars [a,b]
			AIf e a b -> genUnionVars $ genSizedExprVars e : concatMap (map actionVars) [a,b]
			ALoop as -> genUnionVars $ map actionVars as


generate :: Language -> Process ins outs -> String
generate lang (Process process) = flip evalState (startGenS lang) $ do
	genComment $ "Generating from top-level "++show (procName process)
	genProcess process
	liftM (unlines . reverse . gsLines) get
