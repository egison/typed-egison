{-# Language TypeSynonymInstances, FlexibleInstances, GeneralizedNewtypeDeriving,
             MultiParamTypeClasses, UndecidableInstances, DeriveDataTypeable,
             TypeFamilies, TupleSections #-}
{- |
Module      : Language.Egison.Types
Copyright   : Satoshi Egi
Licence     : MIT

This module contains type definitions of Egison Data.
-}

module Language.Egison.Expressions
    (
    -- * Egison expressions
      TopExpr (..)
    , Expr (..)
    , EgisonPattern (..)
    , Arg (..)
    , Index (..)
    , InnerExpr (..)
    , BindingExpr (..)
    , MatchClause (..)
    , MatcherInfo (..)
    , LoopRange (..)
    , PrimitivePatPattern (..)
    , PrimitiveDataPattern (..)
    , Matcher (..)
    , PrimitiveFunc (..)
    , EgisonData (..)
    , showTSV
    -- * Egison values
    , EgisonValue (..)
    , ScalarData (..)
    , PolyExpr (..)
    , TermExpr (..)
    , SymbolExpr (..)
    , Tensor (..)
    , HasTensor (..)
    -- * Tensor
    , initTensor
    , tSize
    , tToList
    , tIndex
    , tref
    , enumTensorIndices
    , tTranspose
    , tTranspose'
    , tFlipIndices
    , appendDFscripts
    , removeDFscripts
    , tMap
    , tMap2
    , tMapN
    , tSum
    , tProduct
    , tContract
    , tContract'
    , tConcat
    , tConcat'
    -- * Scalar
    , symbolScalarData
    , mathExprToEgison
    , egisonToScalarData
    , mathNormalize'
    , mathFold
    , mathSymbolFold
    , mathTermFold
    , mathRemoveZero
    , mathDivide
    , mathPlus
    , mathMult
    , mathNegate
    , mathNumerator
    , mathDenominator
    , extractScalar
    , extractScalar'
    -- * Internal data
    , Object (..)
    , ObjectRef (..)
    , WHNFData (..)
    , Intermediate (..)
    , Inner (..)
    , EgisonWHNF (..)
    -- * Environment
    , Env
    , Var (..)
    , VarWithIndexType (..)
    , VarWithIndices (..)
    , Binding (..)
    , nullEnv
    , extendEnv
    , refVar
    , envType
    , extendEnvImplConv
    , refEnvImplConv
    , refEnvType
    , extendEnvType
    , deleteEnvType
    , extendEnvAbsImplConv
    , refEnvAbsImplConv
    , refEnvDisableTypecheck
    , extendEnvDisableTypecheck
    -- * Pattern matching
    , Match
    , PMMode (..)
    , pmMode
    , MatchingState (..)
    , MatchingTree (..)
    , PatternBinding (..)
    , LoopPatContext (..)
    -- * Errors
    , EgisonError (..)
    , liftError
    -- * Monads
    , EgisonM (..)
    , parallelMapM
    , runEgisonM
    , liftEgisonM
    , fromEgisonM
    , FreshT (..)
    , Fresh (..)
    , MonadFresh (..)
    , runFreshT
    , MatchM (..)
    , matchFail
    , MList (..)
    , fromList
    , fromSeq
    , fromMList
    , msingleton
    , mfoldr
    , mappend
    , mconcat
    , mmap
    , mfor
    -- * Typing
    , isBool
    , isInteger
    , isRational
    , isSymbol
    , isScalar
    , isTensor
    , isTensorWithIndex
    , isBool'
    , isInteger'
    , isRational'
    , isScalar'
    , isFloat'
    , isComplex'
    , isTensor'
    , isTensorWithIndex'
    , isChar'
    , isString'
    , isCollection'
    , isArray'
    , isHash'
    , readUTF8File
    , stringToVar
    -- Types
    , Type(..)
    , TypeVarIndex
    ) where

import Prelude hiding (foldr, mappend, mconcat)

import Control.Exception
import Control.Parallel
import Data.Typeable

import Control.Applicative
import Control.Monad.Except
import Control.Monad.State
import Control.Monad.Reader (ReaderT)
import Control.Monad.Writer (WriterT)
import Control.Monad.Identity
import Control.Monad.Trans.Maybe

import Data.Monoid (Monoid)
import qualified Data.HashMap.Lazy as HL
import qualified Data.Array as Array
import qualified Data.Vector as V
import qualified Data.Sequence as Sq
import Data.Sequence (Seq)
import Data.Foldable (foldr, toList)
import Data.IORef
import Data.Hashable (Hashable)
import Data.HashMap.Strict (HashMap)
import qualified Data.HashMap.Strict as HashMap

import Data.List (intercalate, sort, sortBy, find, findIndex, splitAt, (\\), elem, delete, deleteBy, any, partition, intercalate, elemIndex)
import Data.List.Split (splitOn)
import Data.Text (Text, pack)
import qualified Data.Text as T

import System.IO
import Data.Ratio
import Numeric

import System.IO.Unsafe (unsafePerformIO)
import qualified Data.Map.Strict as MS
import Data.Char (ord)

--
-- Types
--
-- TStar is a kind of wildcard of type.
-- The argument of TFun is Tuple.
-- This is because Egison doesn't do currying, so the arity doesn't change.
-- TCollection is like a list in Haskell.
-- All its element must have the same type.
-- TCFun a b is a function which have arbitrary length args like (+ 1 2 3 4).
-- All TCFun arguments have same type a.
data Type = TypeChar | TypeString | TypeBool | TypeInt | TypeVar TypeVarIndex | TypeStar |
            TypeFun Type Type | TypeTuple [Type] | TypeCollection Type | TypePattern Type |
            TypeMatcher Type | TypeMatcherClause Type
            deriving (Eq)
-- if the head of a TypeVarIndex is capital case, 
-- it is the user defined type name.
type TypeVarIndex = String

instance Show Type where
  show TypeChar = "Char"
  show TypeString = "String"
  show TypeBool = "Bool"
  show TypeInt = "Integer"
  show (TypeVar s) = s
  show TypeStar = "Any"
  show (TypeFun t1 t2) = "(Fun " ++ show t1 ++ " " ++ show t2 ++ ")"
  show (TypeTuple ts) = "(Tuple" ++ (foldl (++) "" (map (\x -> " " ++ show x) ts)) ++ ")"
  show (TypeCollection t) = "(Collection " ++ show t ++ ")"
  show (TypePattern t) = "(Pattern " ++ show t ++ ")"
  show (TypeMatcher t) = "(Matcher " ++ show t ++ ")"
  show (TypeMatcherClause t) = "(MatcherClause " ++ show t ++ ")"

--
-- Expressions
--

data TopExpr =
    Define VarWithIndexType Expr
  | Redefine VarWithIndexType Expr
  | Test Expr
  | Execute Expr
    -- temporary : we will replace load to import and export
  | LoadFile String
  | Load String
  | ImplicitConversion Type Type Expr
  | AbsoluteImplicitConversion Type Type Expr
  | DefineTypeOf Var Type
  | DefineADT String [(String,Type)]
  | PrintTypeOf Expr
  | DisableTypecheckOf Var
 deriving (Show, Eq)

data Expr =
    CharExpr Char
  | StringExpr Text
  | BoolExpr Bool
  | IntegerExpr Integer
  | FloatExpr Double Double
  | VarExpr Var
  | FreshVarExpr
  | IndexedExpr Bool Expr [Index Expr]
  | SubrefsExpr Bool Expr Expr
  | SuprefsExpr Bool Expr Expr
  | UserrefsExpr Bool Expr Expr
  | PowerExpr Expr Expr
  | InductiveDataExpr String [Expr]
  | TupleExpr [Expr]
  | CollectionExpr [InnerExpr]
  | ArrayExpr [Expr]
  | HashExpr [(Expr, Expr)]
  | VectorExpr [Expr]

  | LambdaExpr [Arg] Expr
  | MemoizedLambdaExpr [String] Expr
  | MemoizeExpr [(Expr, Expr, Expr)] Expr
  | CambdaExpr String Expr
  | ProcedureExpr [String] Expr
  | MacroExpr [String] Expr
  | PatternFunctionExpr [String] EgisonPattern
  
  | IfExpr Expr Expr Expr
  | LetRecExpr [BindingExpr] Expr
  | LetExpr [BindingExpr] Expr
  | LetStarExpr [BindingExpr] Expr
  | WithSymbolsExpr [String] Expr

  | MatchExpr Expr Expr [MatchClause]
  | MatchAllExpr Expr Expr MatchClause
  | MatchLambdaExpr Expr [MatchClause]
  | MatchAllLambdaExpr Expr MatchClause

  | NextMatchExpr Expr Expr [MatchClause]
  | NextMatchAllExpr Expr Expr MatchClause
  | NextMatchLambdaExpr Expr [MatchClause]
  | NextMatchAllLambdaExpr Expr MatchClause

  | MatcherBFSExpr MatcherInfo
  | MatcherDFSExpr MatcherInfo
  | AlgebraicDataMatcherExpr [(String, [Expr])]

  | QuoteExpr Expr
  | QuoteFunctionExpr Expr
  
  | WedgeExpr Expr
  | WedgeApplyExpr Expr Expr

  | DoExpr [BindingExpr] Expr
  | IoExpr Expr
    
  | SeqExpr Expr Expr
  | ApplyExpr Expr Expr
  | CApplyExpr Expr Expr
  | PartialExpr Integer Expr
  | PartialVarExpr Integer
  | RecVarExpr

  | GenerateArrayExpr Expr (Expr, Expr)
  | ArrayBoundsExpr Expr
  | ArrayRefExpr Expr Expr

  | ParExpr Expr Expr
  | PseqExpr Expr Expr
  | PmapExpr Expr Expr

  | GenerateTensorExpr Expr Expr
  | TensorExpr Expr Expr Expr Expr
  | TensorContractExpr Expr Expr
  | TensorMapExpr Expr Expr
  | TensorMap2Expr Expr Expr Expr
  | TransposeExpr Expr Expr
  | FlipIndicesExpr Expr

  | FunctionExpr [Expr]

  | SomethingExpr
  | UndefinedExpr
 deriving (Show, Eq)

data Arg =
    ScalarArg String
  | InvertedScalarArg String
  | TensorArg String
 deriving (Eq)

instance Show Arg where
  show (TensorArg s) = "$" ++ s

data Index a =
    Subscript a
  | Superscript a
  | SupSubscript a
  | MultiSubscript a a
  | MultiSuperscript a a
  | DFscript Integer Integer -- DifferentialForm
  | Userscript a
 deriving (Eq)

data InnerExpr =
    ElementExpr Expr
  | SubCollectionExpr Expr
 deriving (Show, Eq)

type BindingExpr = ([Var], Expr)
type MatchClause = (EgisonPattern, Expr)
type MatcherInfo = [(PrimitivePatPattern, Expr, [(PrimitiveDataPattern, Expr)])]

data EgisonPattern =
    WildCard
  | PatVar Var
  | ValuePat Expr
  | PredPat Expr
  | IndexedPat EgisonPattern [Expr]
  -- | LetPat [BindingExpr] EgisonPattern
  | NotPat EgisonPattern
  | AndPat [EgisonPattern]
  | OrPat [EgisonPattern]
  | OrderedOrPat [EgisonPattern]
  | TuplePat [EgisonPattern]
  | InductivePat String [EgisonPattern]
  | LoopPat Var LoopRange EgisonPattern EgisonPattern
  | ContPat
  | PApplyPat Expr [EgisonPattern]
  | VarPat String
  -- For symbolic computing
  | DApplyPat EgisonPattern [EgisonPattern]
  | DivPat EgisonPattern EgisonPattern
  | PlusPat [EgisonPattern]
  | MultPat [EgisonPattern]
  | PowerPat EgisonPattern EgisonPattern
 deriving (Show, Eq)

data LoopRange = LoopRange Expr Expr EgisonPattern
 deriving (Show, Eq)

data PrimitivePatPattern =
    PPWildCard
  | PPPatVar
  | PPValuePat String
  | PPInductivePat String [PrimitivePatPattern]
 deriving (Show, Eq)

data PrimitiveDataPattern =
    PDWildCard
  | PDPatVar String
  | PDInductivePat String [PrimitiveDataPattern]
  | PDTuplePat [PrimitiveDataPattern]
  | PDEmptyPat
  | PDConsPat PrimitiveDataPattern PrimitiveDataPattern
  | PDSnocPat PrimitiveDataPattern PrimitiveDataPattern
  | PDConstantPat Expr
 deriving (Show, Eq)

--
-- Values
--

data EgisonValue =
    World
  | Char Char
  | String Text
  | Bool Bool
  | ScalarData ScalarData
  | TensorData (Tensor EgisonValue)
  | Float Double Double
  | InductiveData String [EgisonValue]
  | Tuple [EgisonValue]
  | Collection (Seq EgisonValue)
  | Array (Array.Array Integer EgisonValue)
  | IntHash (HashMap Integer EgisonValue)
  | CharHash (HashMap Char EgisonValue)
  | StrHash (HashMap Text EgisonValue)
  | UserMatcher Env PMMode MatcherInfo
  | Func (Maybe Var) Env [String] Expr
  | PartialFunc Env Integer Expr | CFunc (Maybe Var) Env String Expr | MemoizedFunc (Maybe Var) ObjectRef (IORef (HashMap [Integer] ObjectRef)) Env [String] Expr
  | Proc (Maybe String) Env [String] Expr
  | Macro [String] Expr
  | PatternFunc Env [String] EgisonPattern
  | PrimitiveFunc String PrimitiveFunc
  | IOFunc (EgisonM WHNFData)
  | QuotedFunc EgisonValue
  | Port Handle
  | Something
  | Undefined
  | EOF

--
-- Scalar and Tensor Types
--

data ScalarData =
    Div PolyExpr PolyExpr
 deriving (Eq)

newtype PolyExpr =
    Plus [TermExpr]

data TermExpr =
    Term Integer [(SymbolExpr, Integer)]

data SymbolExpr =
    Symbol String String [Index ScalarData] -- ID, Name, Indices
  | Apply EgisonValue [ScalarData]
  | Quote ScalarData
  | FunctionData (Maybe String) [EgisonValue] [Index ScalarData]
 deriving (Eq)

instance Eq PolyExpr where
  (Plus []) == (Plus []) = True
  (Plus (x:xs)) == (Plus ys) =
    case elemIndex x ys of
      Just i -> let (hs, _:ts) = splitAt i ys in
                  Plus xs == Plus (hs ++ ts)
      Nothing -> False
  _ == _ = False

instance Eq TermExpr where
  (Term a []) == (Term b [])
    | a /= b =  False
    | otherwise = True
  (Term a ((Quote x, n):xs)) == (Term b ys)
    | (a /= b) && (a /= negate b) =  False
    | otherwise = case elemIndex (Quote x, n) ys of
                    Just i -> let (hs, _:ts) = splitAt i ys in
                                Term a xs == Term b (hs ++ ts)
                    Nothing -> case elemIndex (Quote (mathNegate x), n) ys of
                                 Just i -> let (hs, _:ts) = splitAt i ys in
                                             if even n
                                               then Term a xs == Term b (hs ++ ts)
                                               else Term (negate a) xs == Term b (hs ++ ts)
                                 Nothing -> False
  (Term a (x:xs)) == (Term b ys)
    | (a /= b) && (a /= negate b) =  False
    | otherwise = case elemIndex x ys of
                    Just i -> let (hs, _:ts) = splitAt i ys in
                                Term a xs == Term b (hs ++ ts)
                    Nothing -> False
  _ == _ = False


data Tensor a =
    Tensor [Integer] (V.Vector a) [Index EgisonValue]
  | Scalar a
 deriving (Show)

class HasTensor a where
  tensorElems :: a -> V.Vector a
  tensorSize :: a -> [Integer]
  tensorIndices :: a -> [Index EgisonValue]
  fromTensor :: Tensor a -> EgisonM a
  toTensor :: a -> EgisonM (Tensor a)
  undef :: a

instance HasTensor EgisonValue where
  tensorElems (TensorData (Tensor _ xs _)) = xs
  tensorSize (TensorData (Tensor ns _ _)) = ns
  tensorIndices (TensorData (Tensor _ _ js)) = js
  fromTensor t@Tensor{} = return $ TensorData t
  fromTensor (Scalar x) = return x
  toTensor (TensorData t) = return t
  toTensor x = return $ Scalar x
  undef = Undefined

instance HasTensor WHNFData where
  tensorElems (Intermediate (ITensor (Tensor _ xs _))) = xs
  tensorSize (Intermediate (ITensor (Tensor ns _ _))) = ns
  tensorIndices (Intermediate (ITensor (Tensor _ _ js))) = js
  fromTensor t@Tensor{} = return $ Intermediate $ ITensor t
  fromTensor (Scalar x) = return x
  toTensor (Intermediate (ITensor t)) = return t
  toTensor x = return $ Scalar x
  undef = Value Undefined

--
-- Scalars
--

symbolScalarData :: String -> String -> EgisonValue
symbolScalarData id name = ScalarData (Div (Plus [Term 1 [(Symbol id name [], 1)]]) (Plus [Term 1 []]))

getSymId :: EgisonValue -> String
getSymId (ScalarData (Div (Plus [Term 1 [(Symbol id name [], 1)]]) (Plus [Term 1 []]))) = id

mathExprToEgison :: ScalarData -> EgisonValue
mathExprToEgison (Div p1 p2) = InductiveData "Div" [polyExprToEgison p1, polyExprToEgison p2]

polyExprToEgison :: PolyExpr -> EgisonValue
polyExprToEgison (Plus ts) = InductiveData "Plus" [Collection (Sq.fromList (map termExprToEgison ts))]

termExprToEgison :: TermExpr -> EgisonValue
termExprToEgison (Term a xs) = InductiveData "Term" [toEgison a, Collection (Sq.fromList (map symbolExprToEgison xs))]

symbolExprToEgison :: (SymbolExpr, Integer) -> EgisonValue
symbolExprToEgison (Symbol id x js, n) = Tuple [InductiveData "Symbol" [symbolScalarData id x, f js], toEgison n]
 where
  f js = Collection (Sq.fromList (map (\j -> case j of
                                               Superscript k -> InductiveData "Sup" [ScalarData k]
                                               Subscript k -> InductiveData "Sub" [ScalarData k]
                                               Userscript k -> InductiveData "User" [ScalarData k]
                                      ) js))
symbolExprToEgison (Apply fn mExprs, n) = Tuple [InductiveData "Apply" [fn, Collection (Sq.fromList (map mathExprToEgison mExprs))], toEgison n]
symbolExprToEgison (Quote mExpr, n) = Tuple [InductiveData "Quote" [mathExprToEgison mExpr], toEgison n]
symbolExprToEgison (FunctionData ms args js, n) = case ms of
                                                    Just name -> Tuple [InductiveData "Function" [(String $ (T.pack) name), Collection (Sq.fromList args), f js], toEgison n]
                                                    Nothing -> Tuple [InductiveData "Function" [(String $ (T.pack) ""), Collection (Sq.fromList args), f js], toEgison n]
 where
  f js = Collection (Sq.fromList (map (\j -> case j of
                                               Superscript k -> InductiveData "Sup" [ScalarData k]
                                               Subscript k -> InductiveData "Sub" [ScalarData k]
                                               Userscript k -> InductiveData "User" [ScalarData k]
                                      ) js))

egisonToScalarData :: EgisonValue -> EgisonM ScalarData
egisonToScalarData (InductiveData "Div" [p1, p2]) = Div <$> egisonToPolyExpr p1 <*> egisonToPolyExpr p2
egisonToScalarData p1@(InductiveData "Plus" _) = Div <$> egisonToPolyExpr p1 <*> return (Plus [Term 1 []])
egisonToScalarData t1@(InductiveData "Term" _) = do
  t1' <- egisonToTermExpr t1
  return $ Div (Plus [t1']) (Plus [Term 1 []])
egisonToScalarData s1@(InductiveData "Symbol" _) = do
  s1' <- egisonToSymbolExpr (Tuple [s1, toEgison (1 ::Integer)])
  return $ Div (Plus [Term 1 [s1']]) (Plus [Term 1 []])
egisonToScalarData s1@(InductiveData "Apply" _) = do
  s1' <- egisonToSymbolExpr (Tuple [s1, toEgison (1 :: Integer)])
  return $ Div (Plus [Term 1 [s1']]) (Plus [Term 1 []])
egisonToScalarData s1@(InductiveData "Quote" _) = do
  s1' <- egisonToSymbolExpr (Tuple [s1, toEgison (1 :: Integer)])
  return $ Div (Plus [Term 1 [s1']]) (Plus [Term 1 []])
egisonToScalarData s1@(InductiveData "Function" _) = do
  s1' <- egisonToSymbolExpr (Tuple [s1, toEgison (1 :: Integer)])
  return $ Div (Plus [Term 1 [s1']]) (Plus [Term 1 []])
egisonToScalarData val = liftError $ throwError $ TypeMismatch "math expression" (Value val)

egisonToPolyExpr :: EgisonValue -> EgisonM PolyExpr
egisonToPolyExpr (InductiveData "Plus" [Collection ts]) = Plus <$> mapM egisonToTermExpr (toList ts)
egisonToPolyExpr val = liftError $ throwError $ TypeMismatch "math poly expression" (Value val)

egisonToTermExpr :: EgisonValue -> EgisonM TermExpr
egisonToTermExpr (InductiveData "Term" [n, Collection ts]) = Term <$> fromEgison n <*> mapM egisonToSymbolExpr (toList ts)
egisonToTermExpr val = liftError $ throwError $ TypeMismatch "math term expression" (Value val)

egisonToSymbolExpr :: EgisonValue -> EgisonM (SymbolExpr, Integer)
egisonToSymbolExpr (Tuple [InductiveData "Symbol" [x, Collection seq], n]) = do
  let js = toList seq
  js' <- mapM (\j -> case j of
                         InductiveData "Sup" [ScalarData k] -> return (Superscript k)
                         InductiveData "Sub" [ScalarData k] -> return (Subscript k)
                         InductiveData "User" [ScalarData k] -> return (Userscript k)
                         _ -> liftError $ throwError $ TypeMismatch "math symbol expression" (Value j)
               ) js
  n' <- fromEgison n
  case x of
    (ScalarData (Div (Plus [Term 1 [(Symbol id name [], 1)]]) (Plus [Term 1 []]))) ->
      return (Symbol id name js', n')
egisonToSymbolExpr (Tuple [InductiveData "Apply" [fn, Collection mExprs], n]) = do
  mExprs' <- mapM egisonToScalarData (toList mExprs)
  n' <- fromEgison n
  return (Apply fn mExprs', n')
egisonToSymbolExpr (Tuple [InductiveData "Quote" [mExpr], n]) = do
  mExpr' <- egisonToScalarData mExpr
  n' <- fromEgison n
  return (Quote mExpr', n')
egisonToSymbolExpr (Tuple [InductiveData "Function" [(String name), args, Collection seq], n]) = do
  let js = toList seq
  js' <- mapM (\j -> case j of
                         InductiveData "Sup" [ScalarData k] -> return (Superscript k)
                         InductiveData "Sub" [ScalarData k] -> return (Subscript k)
                         InductiveData "User" [ScalarData k] -> return (Userscript k)
                         _ -> liftError $ throwError $ TypeMismatch "math symbol expression" (Value j)
               ) js
  n' <- fromEgison n
  return (let (Collection seq) = args in case (T.unpack name) of
              "" -> (FunctionData Nothing (toList seq) js', n')
              s -> (FunctionData (Just s) (toList seq) js', n'))
egisonToSymbolExpr val = liftError $ throwError $ TypeMismatch "math symbol expression" (Value val)

mathNormalize' :: ScalarData -> ScalarData
mathNormalize' mExpr = mathDivide (mathRemoveZero (mathFold (mathRemoveZeroSymbol mExpr)))

termsGcd :: [TermExpr] -> TermExpr
termsGcd (t:ts) = f t ts
 where
  f :: TermExpr -> [TermExpr] -> TermExpr
  f ret [] =  ret
  f (Term a xs) (Term b ys:ts) =
    f (Term (gcd a b) (g xs ys)) ts
  g :: [(SymbolExpr, Integer)] -> [(SymbolExpr, Integer)] -> [(SymbolExpr, Integer)]
  g [] ys = []
  g ((x, n):xs) ys = let (z, m) = h (x, n) ys in
    if m == 0 then g xs ys else (z, m):g xs ys
  h :: (SymbolExpr, Integer) -> [(SymbolExpr, Integer)] -> (SymbolExpr, Integer)
  h (x, n) [] = (x, 0)
  h (Quote x, n) ((Quote y, m):ys)
    | x == y = (Quote x, min n m)
    | x == mathNegate y = (Quote x, min n m)
    | otherwise = h (Quote x, n) ys
  h (x, n) ((y, m):ys) = if x == y
                         then (x, min n m)
                         else h (x, n) ys

mathDivide :: ScalarData -> ScalarData
mathDivide (Div (Plus ts1) (Plus [])) = Div (Plus ts1) (Plus [])
mathDivide (Div (Plus []) (Plus ts2)) = Div (Plus []) (Plus ts2)
mathDivide (Div (Plus ts1) (Plus ts2)) =
  let z = termsGcd (ts1 ++ ts2) in
  case z of
--    (Term 1 []) -> (Div (Plus ts1) (Plus ts2))
    (Term c zs) -> case ts2 of
      [Term a _] -> if a < 0
                      then (Div (Plus (map (\t -> mathDivideTerm t (Term (-1 * c) zs)) ts1)) (Plus (map (\t -> mathDivideTerm t (Term (-1 * c) zs)) ts2)))
                      else (Div (Plus (map (\t -> mathDivideTerm t z) ts1)) (Plus (map (\t -> mathDivideTerm t z) ts2)))
      _ -> (Div (Plus (map (\t -> mathDivideTerm t z) ts1)) (Plus (map (\t -> mathDivideTerm t z) ts2)))

mathDivideTerm :: TermExpr -> TermExpr -> TermExpr
mathDivideTerm (Term a xs) (Term b ys) =
  let (sgn, zs) = f 1 xs ys in
  Term (sgn * div a b) zs
 where
  f :: Integer -> [(SymbolExpr, Integer)] -> [(SymbolExpr, Integer)] -> (Integer, [(SymbolExpr, Integer)])
  f sgn xs [] = (sgn, xs)
  f sgn xs ((y, n):ys) =
    let (sgns, zs) = unzip (map (\(x, m) -> (g (x, m) (y, n))) xs) in
    f (sgn * product sgns) zs ys
  g :: (SymbolExpr, Integer) -> (SymbolExpr, Integer) -> (Integer, (SymbolExpr, Integer))
  g (Quote x, n) (Quote y, m)
    | x == y = (1, (Quote x, n - m))
    | x == mathNegate y = if even m then (1, (Quote x, n - m)) else (-1, (Quote x, n - m))
    | otherwise = (1, (Quote x, n))
  g (x, n) (y, m) =
    if x == y
    then (1, (x, n - m))
    else (1, (x, n))
              
mathRemoveZeroSymbol :: ScalarData -> ScalarData
mathRemoveZeroSymbol (Div (Plus ts1) (Plus ts2)) =
  let p x = case x of
              (_, 0) -> False
              _ -> True in
  let ts1' = map (\(Term a xs) -> Term a (filter p xs)) ts1 in
  let ts2' = map (\(Term a xs) -> Term a (filter p xs)) ts2 in
    Div (Plus ts1') (Plus ts2')

mathRemoveZero :: ScalarData -> ScalarData
mathRemoveZero (Div (Plus ts1) (Plus ts2)) =
  let ts1' = filter (\(Term a _) -> a /= 0) ts1 in
  let ts2' = filter (\(Term a _) -> a /= 0) ts2 in
    case ts1' of
      [] -> Div (Plus []) (Plus [Term 1 []])
      _ -> Div (Plus ts1') (Plus ts2')

mathFold :: ScalarData -> ScalarData
mathFold mExpr = mathTermFold (mathSymbolFold (mathTermFold mExpr))

mathSymbolFold :: ScalarData -> ScalarData
mathSymbolFold (Div (Plus ts1) (Plus ts2)) = Div (Plus (map f ts1)) (Plus (map f ts2))
 where
  f :: TermExpr -> TermExpr
  f (Term a xs) = let (ys, sgns) = unzip $ g [] xs
                    in Term (product sgns * a) ys
  g :: [((SymbolExpr, Integer),Integer)] -> [(SymbolExpr, Integer)] -> [((SymbolExpr, Integer),Integer)]
  g ret [] = ret
  g ret ((x, n):xs) =
    if any (p (x, n)) ret
      then g (map (h (x, n)) ret) xs
      else g (ret ++ [((x, n), 1)]) xs
  p :: (SymbolExpr, Integer) -> ((SymbolExpr, Integer), Integer) -> Bool
  p (Quote x, _) ((Quote y, _),_) = (x == y) || (mathNegate x == y)
  p (x, _) ((y, _),_) = x == y
  h :: (SymbolExpr, Integer) -> ((SymbolExpr, Integer), Integer) -> ((SymbolExpr, Integer), Integer)
  h (Quote x, n) ((Quote y, m), sgn)
    | x == y = ((Quote y, m + n), sgn)
    | x == mathNegate y = if even n then ((Quote y, m + n), sgn) else ((Quote y, m + n), -1 * sgn)
    | otherwise = ((Quote y, m), sgn)
  h (x, n) ((y, m), sgn) = if x == y
                             then ((y, m + n), sgn)
                             else ((y, m), sgn)

mathTermFold :: ScalarData -> ScalarData
mathTermFold (Div (Plus ts1) (Plus ts2)) = Div (Plus (f ts1)) (Plus (f ts2))
 where
  f :: [TermExpr] -> [TermExpr]
  f = f' []
  f' :: [TermExpr] -> [TermExpr] -> [TermExpr]
  f' ret [] = ret
  f' ret (Term a xs:ts) =
    if any (\(Term _ ys) -> (fst (p 1 xs ys))) ret
      then f' (map (g (Term a xs)) ret) ts
      else f' (ret ++ [Term a xs]) ts
  g :: TermExpr -> TermExpr -> TermExpr
  g (Term a xs) (Term b ys) = let (c, sgn) = p 1 xs ys in
                                if c
                                  then Term ((sgn * a) + b) ys
                                  else Term b ys
  p :: Integer -> [(SymbolExpr, Integer)] -> [(SymbolExpr, Integer)] -> (Bool, Integer)
  p sgn [] [] = (True, sgn)
  p sgn [] _ = (False, 0)
  p sgn ((x, n):xs) ys =
    let (b, ys', sgn2) = q (x, n) [] ys in
      if b 
        then p (sgn * sgn2) xs ys'
        else (False, 0)
  q :: (SymbolExpr, Integer) -> [(SymbolExpr, Integer)] -> [(SymbolExpr, Integer)] -> (Bool, [(SymbolExpr, Integer)], Integer)
  q _ _ [] = (False, [], 1)
  q (Quote x, n) ret ((Quote y, m):ys)
    | (x == y) && (n == m) = (True, ret ++ ys, 1)
    | (mathNegate x == y) && (n == m) = if even n then (True, ret ++ ys, 1) else (True, ret ++ ys, -1)
    | otherwise = q (Quote x, n) (ret ++ [(Quote y, m)]) ys
  q (Quote x, n) ret ((y,m):ys) = q (Quote x, n) (ret ++ [(y, m)]) ys
  q (x, n) ret ((y, m):ys) = if (x == y) && (n == m)
                               then (True, ret ++ ys, 1)
                               else q (x, n) (ret ++ [(y, m)]) ys

--
--  Arithmetic operations
--

mathPlus :: ScalarData -> ScalarData -> ScalarData
mathPlus (Div m1 n1) (Div m2 n2) = mathNormalize' $ Div (mathPlusPoly (mathMultPoly m1 n2) (mathMultPoly m2 n1)) (mathMultPoly n1 n2)

mathPlusPoly :: PolyExpr -> PolyExpr -> PolyExpr
mathPlusPoly (Plus ts1) (Plus ts2) = Plus (ts1 ++ ts2)

mathMult :: ScalarData -> ScalarData -> ScalarData
mathMult (Div m1 n1) (Div m2 n2) = mathNormalize' $ Div (mathMultPoly m1 m2) (mathMultPoly n1 n2)

mathMult' :: ScalarData -> ScalarData -> ScalarData
mathMult' (Div m1 n1) (Div m2 n2) = Div (mathMultPoly m1 m2) (mathMultPoly n1 n2)

mathMultPoly :: PolyExpr -> PolyExpr -> PolyExpr
mathMultPoly (Plus []) (Plus _) = Plus []
mathMultPoly (Plus _) (Plus []) = Plus []
mathMultPoly (Plus ts1) (Plus ts2) = foldl mathPlusPoly (Plus []) (map (\(Term a xs) -> (Plus (map (\(Term b ys) -> (Term (a * b) (xs ++ ys))) ts2))) ts1)

mathNegate :: ScalarData -> ScalarData
mathNegate (Div m n) = Div (mathNegate' m) n

mathNegate' :: PolyExpr -> PolyExpr
mathNegate' (Plus ts) = Plus (map (\(Term a xs) -> (Term (negate a) xs)) ts)

mathNumerator :: ScalarData -> ScalarData
mathNumerator (Div m _) = Div m (Plus [Term 1 []])

mathDenominator :: ScalarData -> ScalarData
mathDenominator (Div _ n) = Div n (Plus [Term 1 []])

--
-- ExtractScalar
--

extractScalar :: EgisonValue -> EgisonM ScalarData
extractScalar (ScalarData mExpr) = return mExpr
extractScalar val = throwError $ TypeMismatch "math expression" (Value val)

extractScalar' :: WHNFData -> EgisonM ScalarData
extractScalar' (Value (ScalarData x)) = return x
extractScalar' val = throwError $ TypeMismatch "integer or string" val

--
-- Tensors
--

initTensor :: [Integer] -> [a] -> [EgisonValue] -> [EgisonValue] -> Tensor a
initTensor ns xs sup sub = Tensor ns (V.fromList xs) (map Superscript sup ++ map Subscript sub)

tSize :: Tensor a -> [Integer]
tSize (Tensor ns _ _) = ns
tSize (Scalar _) = []

tToList :: Tensor a -> [a]
tToList (Tensor _ xs _) = V.toList xs
tToList (Scalar x) = [x]

tToVector :: Tensor a -> V.Vector a
tToVector (Tensor _ xs _) = xs
tToVector (Scalar x) = V.fromList [x]

tIndex :: Tensor a -> [Index EgisonValue]
tIndex (Tensor _ _ js) = js
tIndex (Scalar _) = []

tIntRef' :: HasTensor a => Integer -> Tensor a -> EgisonM a
tIntRef' i (Tensor [ary] xs _) = let n = fromIntegral (length [ary]) in
                                     if (0 < i) && (i <= (n + 3)) then fromTensor $ Scalar $ xs V.! fromIntegral (i - 1)
                                                                  else throwError $ TensorIndexOutOfBounds i (n + 3)
tIntRef' i (Tensor (n:ns) xs js) =
  if (0 < i) && (i <= n)
   then let w = fromIntegral (product ns) in
        let ys = V.take w (V.drop (w * (fromIntegral (i - 1))) xs) in
          fromTensor $ Tensor ns ys (cdr js)
   else throwError $ TensorIndexOutOfBounds i n
tIntRef' i _ = throwError $ Default "More indices than the order of the tensor"
 
tIntRef :: HasTensor a => [Integer] -> Tensor a -> EgisonM (Tensor a)
tIntRef [] (Tensor [] xs _)
  | V.length xs == 1 = return $ Scalar (xs V.! 0)
  | otherwise = throwError $ EgisonBug "sevaral elements in scalar tensor"
tIntRef [] t = return t
tIntRef (m:ms) t = tIntRef' m t >>= toTensor >>= tIntRef ms 

tref :: HasTensor a => [Index EgisonValue] -> Tensor a -> EgisonM a
tref [] (Tensor [] xs _)
  | V.length xs == 1 = fromTensor $ Scalar (xs V.! 0)
  | otherwise = throwError $ EgisonBug "sevaral elements in scalar tensor"
tref [] t = fromTensor t
tref (Subscript (ScalarData (Div (Plus [Term m []]) (Plus [Term 1 []]))):ms) t = tIntRef' m t >>= toTensor >>= tref ms
tref (Subscript (ScalarData (Div (Plus []) (Plus [Term 1 []]))):ms) t = tIntRef' 0 t >>= toTensor >>= tref ms
tref (Superscript (ScalarData (Div (Plus [Term m []]) (Plus [Term 1 []]))):ms) t = tIntRef' m t >>= toTensor >>= tref ms
tref (Superscript (ScalarData (Div (Plus []) (Plus [Term 1 []]))):ms) t = tIntRef' 0 t >>= toTensor >>= tref ms
tref (SupSubscript (ScalarData (Div (Plus [Term m []]) (Plus [Term 1 []]))):ms) t = tIntRef' m t >>= toTensor >>= tref ms
tref (SupSubscript (ScalarData (Div (Plus []) (Plus [Term 1 []]))):ms) t = tIntRef' 0 t >>= toTensor >>= tref ms
tref (Subscript (Tuple [mVal, nVal]):ms) t@(Tensor is _ _) = do
  m <- fromEgison mVal
  n <- fromEgison nVal
  if m > n
    then
      fromTensor (Tensor (replicate (length is) 0) V.empty [])
    else do
      ts <- mapM (\i -> tIntRef' i t >>= toTensor >>= tref ms >>= toTensor) [m..n]
      symId <- fresh
      tConcat (Subscript (symbolScalarData "" (":::" ++ symId))) ts >>= fromTensor
tref (Superscript (Tuple [mVal, nVal]):ms) t@(Tensor is _ _) = do
  m <- fromEgison mVal
  n <- fromEgison nVal
  if m > n
    then
      fromTensor (Tensor (replicate (length is) 0) V.empty [])
    else do
      ts <- mapM (\i -> tIntRef' i t >>= toTensor >>= tref ms >>= toTensor) [m..n]
      symId <- fresh
      tConcat (Superscript (symbolScalarData "" (":::" ++ symId))) ts >>= fromTensor
tref (SupSubscript (Tuple [mVal, nVal]):ms) t@(Tensor is _ _) = do
  m <- fromEgison mVal
  n <- fromEgison nVal
  if m > n
    then
      fromTensor (Tensor (replicate (length is) 0) V.empty [])
    else do
      ts <- mapM (\i -> tIntRef' i t >>= toTensor >>= tref ms >>= toTensor) [m..n]
      symId <- fresh
      tConcat (SupSubscript (symbolScalarData "" (":::" ++ symId))) ts >>= fromTensor
tref (s:ms) (Tensor (n:ns) xs js) = do
  let yss = split (product ns) xs
  ts <- mapM (\ys -> tref ms (Tensor ns ys (cdr js))) yss
  mapM toTensor ts >>= tConcat s >>= fromTensor
tref _ t = throwError $ Default "More indices than the order of the tensor"

enumTensorIndices :: [Integer] -> [[Integer]]
enumTensorIndices [] = [[]]
enumTensorIndices (n:ns) = concatMap (\i -> (map (\is -> i:is) (enumTensorIndices ns))) [1..n]

transIndex :: [Index EgisonValue] -> [Index EgisonValue] -> [Integer] -> EgisonM [Integer]
transIndex [] [] is = return is
transIndex (j1:js1) js2 is = do
  let (hjs2, tjs2) = break (\j2 -> j1 == j2) js2
  if tjs2 == []
    then throwError InconsistentTensorIndex
    else do let n = length hjs2 + 1
            rs <- transIndex js1 (hjs2 ++ tail tjs2) (take (n - 1) is ++ drop n is)
            return (nth (fromIntegral n) is:rs)
transIndex _ _ _ = throwError InconsistentTensorSize

tTranspose :: HasTensor a => [Index EgisonValue] -> Tensor a -> EgisonM (Tensor a)
tTranspose is t@(Tensor ns xs js) = do
  ns' <- transIndex js is ns
  xs' <- mapM (transIndex js is) (enumTensorIndices ns') >>= mapM (`tIntRef` t) >>= mapM fromTensor >>= return . V.fromList
  return $ Tensor ns' xs' is

tTranspose' :: HasTensor a => [EgisonValue] -> Tensor a -> EgisonM (Tensor a)
tTranspose' is t@(Tensor ns xs js) = do
  is' <- g is js
  tTranspose is' t
 where
  f :: Index EgisonValue -> EgisonValue
  f (Subscript i) = i
  f (Superscript i) = i
  f (SupSubscript i) = i
  g :: [EgisonValue] -> [Index EgisonValue] -> EgisonM [Index EgisonValue]
  g [] js = return []
  g (i:is) js = case find (\j -> i == f j) js of
                  Nothing ->  throwError InconsistentTensorIndex
                  (Just j') -> do js' <- g is js
                                  return $ j':js'

tFlipIndices :: HasTensor a => Tensor a -> EgisonM (Tensor a)
tFlipIndices (Tensor ns xs js) = return $ Tensor ns xs (map flipIndex js)
 where
  flipIndex (Subscript i) = Superscript i
  flipIndex (Superscript i) = Subscript i
  flipIndex x = x

appendDFscripts :: Integer -> WHNFData -> EgisonM WHNFData
appendDFscripts id (Intermediate (ITensor (Tensor s xs is))) = do
  let k = fromIntegral (length s - length is)
  return $ Intermediate (ITensor (Tensor s xs (is ++ map (DFscript id) [1..k])))
appendDFscripts id (Value (TensorData (Tensor s xs is))) = do
  let k = fromIntegral (length s - length is)
  return $ Value (TensorData (Tensor s xs (is ++ map (DFscript id) [1..k])))
appendDFscripts _ whnf = return whnf

removeDFscripts :: WHNFData -> EgisonM WHNFData
removeDFscripts (Intermediate (ITensor (Tensor s xs is))) = do
  let (ds, js) = partition isDF is
  (Tensor s ys _) <- tTranspose (js ++ ds) (Tensor s xs is)
  return (Intermediate (ITensor (Tensor s ys js)))
 where
  isDF (DFscript _ _) = True
  isDF _ = False
removeDFscripts (Value (TensorData (Tensor s xs is))) = do
  let (ds, js) = partition isDF is
  (Tensor s ys _) <- tTranspose (js ++ ds) (Tensor s xs is)
  return (Value (TensorData (Tensor s ys js)))
 where
  isDF (DFscript _ _) = True
  isDF _ = False
removeDFscripts whnf = return whnf

tMap :: HasTensor a => (a -> EgisonM a) -> Tensor a -> EgisonM (Tensor a)
tMap f (Tensor ns xs js') = do
  let k = fromIntegral $ length ns - length js'
  let js = js' ++ map (DFscript 0) [1..k]
  xs' <- mapM f (V.toList xs) >>= return . V.fromList
  t <- toTensor (V.head xs')
  case t of
    (Tensor ns1 _ js1') -> do
      let k1 = fromIntegral $ length ns1 - length js1'
      let js1 = js1' ++ map (DFscript 0) [1..k1]
      tContract' $ Tensor (ns ++ ns1) (V.concat (V.toList (V.map tensorElems xs'))) (js ++ js1)
    _ -> return $ Tensor ns xs' js
tMap f (Scalar x) = Scalar <$> f x

tMapN :: HasTensor a => ([a] -> EgisonM a) -> [Tensor a] -> EgisonM (Tensor a)
tMapN f ts@(Tensor ns xs js:_) = do
  xs' <- mapM (\is -> mapM (tIntRef is) ts >>= mapM fromTensor >>= f) (enumTensorIndices ns)
  return $ Tensor ns (V.fromList xs') js
tMapN f xs = Scalar <$> (mapM fromTensor xs >>= f)

tMap2 :: HasTensor a => (a -> a -> EgisonM a) -> Tensor a -> Tensor a -> EgisonM (Tensor a)
tMap2 f t1@(Tensor ns1 xs1 js1') t2@(Tensor ns2 xs2 js2') = do
  let k1 = fromIntegral $ length ns1 - length js1'
  let js1 = js1' ++ map (DFscript 0) [1..k1]
  let k2 = fromIntegral $ length ns2 - length js2'
  let js2 = js2' ++ map (DFscript 0) [1..k2]
  let (cjs, tjs1, tjs2) = h js1 js2
  t1' <- tTranspose (cjs ++ tjs1) t1
  t2' <- tTranspose (cjs ++ tjs2) t2
  let cns = take (length cjs) (tSize t1')
  rts1 <- mapM (`tIntRef` t1') (enumTensorIndices cns)
  rts2 <- mapM (`tIntRef` t2') (enumTensorIndices cns)
  rts' <- mapM (\(t1, t2) -> tProduct f t1 t2) (zip rts1 rts2)
  let ret = Tensor (cns ++ tSize (head rts')) (V.concat (map tToVector rts')) (cjs ++ tIndex (head rts'))
  tTranspose (uniq (tDiagIndex (js1 ++ js2))) ret
 where
  h :: [Index EgisonValue] -> [Index EgisonValue] -> ([Index EgisonValue], [Index EgisonValue], [Index EgisonValue])
  h js1 js2 = let cjs = filter (`elem` js2) js1 in
                (cjs, js1 \\ cjs, js2 \\ cjs)
  uniq :: [Index EgisonValue] -> [Index EgisonValue]
  uniq [] = []
  uniq (x:xs) = x:uniq (delete x xs)
tMap2 f t@(Tensor _ _ _) (Scalar x) = tMap (`f` x) t
tMap2 f (Scalar x) t@(Tensor _ _ _) = tMap (f x) t
tMap2 f (Scalar x1) (Scalar x2) = Scalar <$> f x1 x2

tDiag :: HasTensor a => Tensor a -> EgisonM (Tensor a)
tDiag t@(Tensor _ _ js) = do
  case filter (\j -> any (p j) js) js of
    [] -> return t
    xs -> do
      let ys = js \\ (xs ++ map rev xs)
      t2 <- tTranspose (xs ++ map rev xs ++ ys) t
      let (ns1, tmp) = splitAt (length xs) (tSize t2)
      let (_, ns2) = splitAt (length xs) tmp
      ts <- mapM (\is -> tIntRef (is ++ is) t2) (enumTensorIndices ns1)
      return $ Tensor (ns1 ++ ns2) (V.concat (map tToVector ts)) (map g xs ++ ys)
 where
  p :: Index EgisonValue -> Index EgisonValue -> Bool
  p (Superscript i) (Subscript j) = i == j
  p (Subscript i) _ = False
  p _ _ = False
  rev :: Index EgisonValue -> Index EgisonValue
  rev (Superscript i) = Subscript i
  rev (Subscript i) = Superscript i
  g :: Index EgisonValue -> Index EgisonValue
  g (Superscript i) = SupSubscript i
  g (Subscript i) = SupSubscript i
tDiag t = return t

tDiagIndex :: [Index EgisonValue] -> [Index EgisonValue]
tDiagIndex js =
  let xs = filter (\j -> any (p j) js) js in
  let ys = js \\ (xs ++ map rev xs) in
    map g xs ++ ys
 where
  p :: Index EgisonValue -> Index EgisonValue -> Bool
  p (Superscript i) (Subscript j) = i == j
  p (Subscript _) _ = False
  p _ _ = False
  rev :: Index EgisonValue -> Index EgisonValue
  rev (Superscript i) = Subscript i
  rev (Subscript i) = Superscript i
  g :: Index EgisonValue -> Index EgisonValue
  g (Superscript i) = SupSubscript i
  g (Subscript i) = SupSubscript i

tSum :: HasTensor a => (a -> a -> EgisonM a) -> Tensor a -> Tensor a -> EgisonM (Tensor a)
tSum f t1@(Tensor ns1 xs1 js1) t2@(Tensor _ _ _) = do
  t2' <- tTranspose js1 t2
  case t2' of
    (Tensor ns2 xs2 _)
      | ns2 == ns1 -> do ys <- V.mapM (\(x1,x2) -> f x1 x2) (V.zip xs1 xs2)
                         return (Tensor ns1 ys js1)
      | otherwise -> throwError InconsistentTensorSize

tProduct :: HasTensor a => (a -> a -> EgisonM a) -> Tensor a -> Tensor a -> EgisonM (Tensor a)
tProduct f t1''@(Tensor ns1 xs1 js1') t2''@(Tensor ns2 xs2 js2') = do
  let k1 = fromIntegral $ length ns1 - length js1'
  let js1 = js1' ++ map (DFscript 0) [1..k1]
  let k2 = fromIntegral $ length ns2 - length js2'
  let js2 = js2' ++ map (DFscript 0) [1..k2]
  let (cjs1, cjs2, tjs1, tjs2) = h js1 js2
  let t1 = (Tensor ns1 xs1 js1)
  let t2 = (Tensor ns2 xs2 js2)
  case cjs1 of
    [] -> do
      xs' <- mapM (\is -> do let is1 = take (length ns1) is
                             let is2 = take (length ns2) (drop (length ns1) is)
                             x1 <- tIntRef is1 t1 >>= fromTensor
                             x2 <- tIntRef is2 t2 >>= fromTensor
                             f x1 x2) (enumTensorIndices (ns1 ++ ns2)) >>= return . V.fromList
      tContract' (Tensor (ns1 ++ ns2) xs' (js1 ++ js2))
    _ -> do
      t1' <- tTranspose (cjs1 ++ tjs1) t1
      t2' <- tTranspose (cjs2 ++ tjs2) t2
      let (cns1, tns1) = splitAt (length cjs1) (tSize t1')
      let (cns2, tns2) = splitAt (length cjs2) (tSize t2')
      rts' <- mapM (\is -> do rt1 <- tIntRef is t1'
                              rt2 <- tIntRef is t2'
                              tProduct f rt1 rt2) (enumTensorIndices cns1)
      let ret = Tensor (cns1 ++ tSize (head rts')) (V.concat (map tToVector rts')) (map g cjs1 ++ tIndex (head rts'))
      ret2 <- tTranspose (uniq (map g cjs1 ++ tjs1 ++ tjs2)) ret
      return ret2
 where
  h :: [Index EgisonValue] -> [Index EgisonValue] -> ([Index EgisonValue], [Index EgisonValue], [Index EgisonValue], [Index EgisonValue])
  h js1 js2 = let cjs = filter (\j -> any (p j) js2) js1 in
                (cjs, map rev cjs, js1 \\ cjs, js2 \\ map rev cjs)
  p :: Index EgisonValue -> Index EgisonValue -> Bool
  p (Superscript i) (Subscript j) = i == j
  p (Subscript i) (Superscript j) = i == j
  p _ _ = False
  rev :: Index EgisonValue -> Index EgisonValue
  rev (Superscript i) = Subscript i
  rev (Subscript i) = Superscript i
  g :: Index EgisonValue -> Index EgisonValue
  g (Superscript i) = SupSubscript i
  g (Subscript i) = SupSubscript i
  uniq :: [Index EgisonValue] -> [Index EgisonValue]
  uniq [] = []
  uniq (x:xs) = x:uniq (delete x xs)
tProduct f (Scalar x) (Tensor ns xs js) = do
  xs' <- V.mapM (f x) xs
  return $ Tensor ns xs' js
tProduct f (Tensor ns xs js) (Scalar x) = do
  xs' <- V.mapM (`f` x) xs
  return $ Tensor ns xs' js
tProduct f (Scalar x1) (Scalar x2) = Scalar <$> f x1 x2

tContract :: HasTensor a => Tensor a -> EgisonM [Tensor a]
tContract t = do
  t' <- tDiag t
  case t' of
    (Tensor (n:ns) xs (SupSubscript i:js)) -> do
      ts <- mapM (`tIntRef'` t') [1..n]
      tss <- mapM toTensor ts >>= mapM tContract
      return $ concat tss
    _ -> return [t']

tContract' :: HasTensor a => Tensor a -> EgisonM (Tensor a)
tContract' t@(Tensor ns xs js) = do
  case findPairs p js of
    [] -> return t
    ((m,n):_) -> do
      let ns' = (ns !! m):removePairs (m,n) ns
      let js' = (js !! m):removePairs (m,n) js
      let (hjs, mjs, tjs) = removePairs' (m,n) js
      xs' <- mapM (\i -> (tref (hjs ++ [Subscript (ScalarData (Div (Plus [Term i []]) (Plus [Term 1 []])))] ++ mjs
                                    ++ [Subscript (ScalarData (Div (Plus [Term i []]) (Plus [Term 1 []])))] ++ tjs) t))
                  [1..(ns !! m)]
      mapM toTensor xs' >>= tConcat (js !! m) >>= tTranspose (hjs ++ [js !! m] ++ mjs ++ tjs) >>= tContract'
 where
  p :: Index EgisonValue -> Index EgisonValue -> Bool
  p (Superscript i) (Superscript j) = i == j
  p (Subscript i) (Subscript j) = i == j
  p (DFscript i1 j1) (DFscript i2 j2) = (i1 == i2) && (j1 == j2)
  p _ _ = False
tContract' val = return val

-- utility functions for tensors

nth :: Integer -> [a] -> a
nth i xs = xs !! fromIntegral (i - 1)

cdr :: [a] -> [a]
cdr [] = []
cdr (_:ts) = ts

split :: Integer -> V.Vector a -> [V.Vector a]
split w xs
 | V.null xs = []
 | otherwise = let (hs, ts) = V.splitAt (fromIntegral w) xs in
                 hs:split w ts

tConcat :: HasTensor a => Index EgisonValue -> [Tensor a] -> EgisonM (Tensor a)
tConcat s (Tensor ns@(0:_) _ js:_) = return $ Tensor (0:ns) V.empty (s:js)
tConcat s ts@(Tensor ns _ js:_) = return $ Tensor (fromIntegral (length ts):ns) (V.concat (map tToVector ts)) (s:js)
tConcat s ts = do
  ts' <- mapM getScalar ts
  return $ Tensor [fromIntegral (length ts)] (V.fromList ts') [s]

tConcat' :: HasTensor a => [Tensor a] -> EgisonM (Tensor a)
tConcat' (Tensor ns@(0:_) _ _:_) = return $ Tensor (0:ns) V.empty []
tConcat' ts@(Tensor ns v _:_) = return $ Tensor (fromIntegral (length ts):ns) (V.concat (map tToVector ts)) []
tConcat' ts = do
  ts' <- mapM getScalar ts
  return $ Tensor [fromIntegral (length ts)] (V.fromList ts') []

getScalar :: Tensor a -> EgisonM a
getScalar (Scalar x) = return x
getScalar _ = throwError $ Default "Inconsitent Tensor order"

findPairs :: (a -> a -> Bool) -> [a] -> [(Int, Int)]
findPairs p xs = reverse $ findPairs' 0 p xs

findPairs' :: Int -> (a -> a -> Bool) -> [a] -> [(Int, Int)]
findPairs' _ _ [] = []
findPairs' m p (x:xs) = case findIndex (p x) xs of
                    Just i -> (m, m + i + 1):findPairs' (m + 1) p xs
                    Nothing -> findPairs' (m + 1) p xs

removePairs :: (Int, Int) -> [a] -> [a]
removePairs (m, n) xs =
  let (hs, ms, ts) = removePairs' (m, n) xs in
    hs ++ ms ++ ts

removePairs' :: (Int, Int) -> [a] -> ([a],[a],[a])
removePairs' (m, n) xs =           -- (0,1) [i i]
  let (hms, tts) = splitAt n xs in -- [i] [i]
  let ts = tail tts in             -- []
  let (hs, tms) = splitAt m hms in -- [] [i]
  let ms = tail tms in             -- []
    (hs, ms, ts)                   -- [] [] []
--
--
--

type Matcher = EgisonValue

type PrimitiveFunc = WHNFData -> EgisonM WHNFData

-- instance Show Expr where
--   show (CharExpr c) = "c#" ++ [c]
--   show (StringExpr str) = "\"" ++ T.unpack str ++ "\""
--   show (BoolExpr True) = "#t"
--   show (BoolExpr False) = "#f"
--   show (IntegerExpr n) = show n
--   show (FloatExpr x y) = showComplexFloat x y
--   show (VarExpr name) = show name
--   show (PartialVarExpr n) = "%" ++ show n
--   show (FunctionExpr args) = "function [" ++ unwords (map show args) ++ "]"
--   show (ApplyExpr fn (TupleExpr [])) = "(" ++ show fn ++ ")"
--   show (ApplyExpr fn (TupleExpr args)) = "(" ++ show fn ++ " " ++ unwords (map show args) ++ ")"
--   show (ApplyExpr fn arg) = "(" ++ show fn ++ " " ++ show arg ++ ")"
--   show (TupleExpr es) = "[" ++ (intercalate " " (map show es)) ++ "]"
--   show (CollectionExpr es) = "{" ++ (intercalate " " (map show (f es))) ++ "}"
--     where
--       f [] = []
--       f (ElementExpr e:rest) = e:(f rest)
--       f ((SubCollectionExpr (CollectionExpr is)):rest) = f is ++ f rest
--   show (LambdaExpr as e) = "(lambda [" ++ (intercalate " " (map show as)) ++ "] " ++ show e ++ ")"


instance Show EgisonValue where
  show (Char c) = "c#" ++ [c]
  show (String str) = "\"" ++ T.unpack str ++ "\""
  show (Bool True) = "#t"
  show (Bool False) = "#f"
  show (ScalarData mExpr) = show mExpr
--  show (TensorData (Scalar x)) = "invalid scalar:" ++ show x
  show (TensorData (Tensor [_] xs js)) = "[| " ++ unwords (map show (V.toList xs)) ++ " |]" ++ concatMap show js
  show (TensorData (Tensor [0, 0] _ js)) = "[| [|  |] |]" ++ concatMap show js
  show (TensorData (Tensor [i, j] xs js)) = "[| " ++ f (fromIntegral j) (V.toList xs) ++ "|]" ++ concatMap show js
   where
    f j [] = ""
    f j xs = "[| " ++ unwords (map show (take j xs)) ++ " |] " ++ f j (drop j xs)
  show (TensorData (Tensor ns xs js)) = "(tensor {" ++ unwords (map show ns) ++ "} {" ++ unwords (map show (V.toList xs)) ++ "} )" ++ concatMap show js
  show (Float x y) = showComplexFloat x y
  show (InductiveData name []) = "<" ++ name ++ ">"
  show (InductiveData name vals) = "<" ++ name ++ " " ++ unwords (map show vals) ++ ">"
  show (Tuple vals) = "[" ++ unwords (map show vals) ++ "]"
  show (Collection vals) = if Sq.null vals
                             then "{}"
                             else "{" ++ unwords (map show (toList vals)) ++ "}"
  show (Array vals) = "(|" ++ unwords (map show $ Array.elems vals) ++ "|)"
  show (IntHash hash) = "{|" ++ unwords (map (\(key, val) -> "[" ++ show key ++ " " ++ show val ++ "]") $ HashMap.toList hash) ++ "|}"
  show (CharHash hash) = "{|" ++ unwords (map (\(key, val) -> "[" ++ show key ++ " " ++ show val ++ "]") $ HashMap.toList hash) ++ "|}"
  show (StrHash hash) = "{|" ++ unwords (map (\(key, val) -> "[\"" ++ T.unpack key ++ "\" " ++ show val ++ "]") $ HashMap.toList hash) ++ "|}"
  show (UserMatcher _ BFSMode _) = "#<matcher-bfs>"
  show (UserMatcher _ DFSMode _) = "#<matcher-dfs>"
  show (Func Nothing _ args _) = "(lambda [" ++ unwords (map show args) ++ "] ...)"
  show (Func (Just name) _ _ _) = show name
  show (PartialFunc _ n expr) = show n ++ "#" ++ show expr
  show (CFunc Nothing _ name _) = "(cambda " ++ name ++ " ...)"
  show (CFunc (Just name) _ _ _) = show name
  show (MemoizedFunc Nothing _ _ _ names _) = "(memoized-lambda [" ++ unwords names ++ "] ...)"
  show (MemoizedFunc (Just name) _ _ _ names _) = show name
  show (Proc Nothing _ names _) = "(procedure [" ++ unwords names ++ "] ...)"
  show (Proc (Just name) _ _ _) = name
  show (Macro names _) = "(macro [" ++ unwords names ++ "] ...)"
  show (PatternFunc _ _ _) = "#<pattern-function>"
  show (PrimitiveFunc name _) = "#<primitive-function " ++ name ++ ">"
  show (IOFunc _) = "#<io-function>"
  show (QuotedFunc _) = "#<quoted-function>"
  show (Port _) = "#<port>"
  show Something = "something"
  show Undefined = "undefined"
  show World = "#<world>"
  show EOF = "#<eof>"

-- instance Show Arg where
--   show (ScalarArg name) = "$" ++ name
--   show (InvertedScalarArg name) = "*$" ++ name
--   show (TensorArg name) = "%" ++ name

instance Show ScalarData where
  show (Div p1 (Plus [Term 1 []])) = show p1
  show (Div p1 p2) = "(/ " ++ show p1 ++ " " ++ show p2 ++ ")"

instance Show PolyExpr where
  show (Plus []) = "0"
  show (Plus [t]) = show t
  show (Plus ts) = "(+ " ++ unwords (map show ts)  ++ ")"

instance Show TermExpr where
  show (Term a []) = show a
  show (Term 1 [x]) = showPoweredSymbol x
  show (Term 1 xs) = "(* " ++ unwords (map showPoweredSymbol xs) ++ ")"
  show (Term a xs) = "(* " ++ show a ++ " " ++ unwords (map showPoweredSymbol xs) ++ ")"

showPoweredSymbol :: (SymbolExpr, Integer) -> String
showPoweredSymbol (x, 1) = show x
showPoweredSymbol (x, n) = show x ++ "^" ++ show n

instance Show SymbolExpr where
  show (Symbol _ (':':':':':':_) []) = "#"
  show (Symbol _ s []) = s
  show (Symbol _ s js) = s ++ concatMap show js
  show (Apply fn mExprs) = "(" ++ show fn ++ " " ++ unwords (map show mExprs) ++ ")"
  show (Quote mExprs) = "'" ++ show mExprs
  show (FunctionData ms args js) = case ms of
                                  Nothing -> "(function [" ++ unwords (map show args) ++ "])" ++ concatMap show js
                                  Just name -> name ++ concatMap show js

showComplex :: (Num a, Eq a, Ord a, Show a) => a -> a -> String
showComplex x 0 = show x
showComplex 0 y = show y ++ "i"
showComplex x y = show x ++ (if y > 0 then "+" else "") ++ show y ++ "i"

showComplexFloat :: Double -> Double -> String
showComplexFloat x 0.0 = showFFloat Nothing x ""
showComplexFloat 0.0 y = showFFloat Nothing y "i"
showComplexFloat x y = showFFloat Nothing x "" ++ if y > 0
                                                    then "+" ++ showFFloat Nothing y "i"
                                                    else showFFloat Nothing y "i"

showTSV :: EgisonValue -> String
showTSV (Tuple (val:vals)) = foldl (\r x -> r ++ "\t" ++ x) (show val) (map show vals)
showTSV (Collection vals) = intercalate "\t" (map show (toList vals))
showTSV val = show val

instance Eq EgisonValue where
 (Char c) == (Char c') = c == c'
 (String str) == (String str') = str == str'
 (Bool b) == (Bool b') = b == b'
 (ScalarData x) == (ScalarData y) = x == y
 (TensorData (Tensor js xs _)) == (TensorData (Tensor js' xs' _)) = (js == js') && (xs == xs')
 (Float x y) == (Float x' y') = (x == x') && (y == y')
 (InductiveData name vals) == (InductiveData name' vals') = (name == name') && (vals == vals')
 (Tuple vals) == (Tuple vals') = vals == vals'
 (Collection vals) == (Collection vals') = vals == vals'
 (Array vals) == (Array vals') = vals == vals'
 (IntHash vals) == (IntHash vals') = vals == vals'
 (CharHash vals) == (CharHash vals') = vals == vals'
 (StrHash vals) == (StrHash vals') = vals == vals'
 (PrimitiveFunc name1 _) == (PrimitiveFunc name2 _) = name1 == name2
 -- Temporary: searching a better solution
 (Func Nothing _ xs1 expr1) == (Func Nothing _ xs2 expr2) = (xs1 == xs2) && (expr1 == expr2)
 (Func (Just name1) _ _ _) == (Func (Just name2) _ _ _) = name1 == name2
 (CFunc Nothing _ x1 expr1) == (CFunc Nothing _ x2 expr2) = (x1 == x2) && (expr1 == expr2)
 (CFunc (Just name1) _ _ _) == (CFunc (Just name2) _ _ _) = name1 == name2
 (Macro xs1 expr1) == (Macro xs2 expr2) = (xs1 == xs2) && (expr1 == expr2)
 _ == _ = False

--
-- Egison data and Haskell data
--
class EgisonData a where
  toEgison :: a -> EgisonValue
  fromEgison :: EgisonValue -> EgisonM a

instance EgisonData Char where
  toEgison = Char
  fromEgison = liftError . fromCharValue

instance EgisonData Text where
  toEgison = String
  fromEgison = liftError . fromStringValue

instance EgisonData Bool where
  toEgison = Bool
  fromEgison = liftError . fromBoolValue

instance EgisonData Integer where
  toEgison 0 = ScalarData $ mathNormalize' (Div (Plus []) (Plus [Term 1 []]))
  toEgison i = ScalarData $ mathNormalize' (Div (Plus [Term i []]) (Plus [Term 1 []]))
  fromEgison = liftError . fromIntegerValue

instance EgisonData Rational where
  toEgison r = ScalarData $ mathNormalize' (Div (Plus [Term (numerator r) []]) (Plus [Term (denominator r) []]))
  fromEgison = liftError . fromRationalValue

instance EgisonData Double where
  toEgison f = Float f 0
  fromEgison = liftError . fromFloatValue

instance EgisonData Handle where
  toEgison = Port
  fromEgison = liftError . fromPortValue

instance (EgisonData a) => EgisonData [a] where
  toEgison xs = Collection $ Sq.fromList (map toEgison xs)
  fromEgison (Collection seq) = mapM fromEgison (toList seq)
  fromEgison val = liftError $ throwError $ TypeMismatch "collection" (Value val)

instance EgisonData () where
  toEgison () = Tuple []
  fromEgison (Tuple []) = return ()
  fromEgison val = liftError $ throwError $ TypeMismatch "zero element tuple" (Value val)

instance (EgisonData a, EgisonData b) => EgisonData (a, b) where
  toEgison (x, y) = Tuple [toEgison x, toEgison y]
  fromEgison (Tuple [x, y]) = liftM2 (,) (fromEgison x) (fromEgison y)
  fromEgison val = liftError $ throwError $ TypeMismatch "two elements tuple" (Value val)

instance (EgisonData a, EgisonData b, EgisonData c) => EgisonData (a, b, c) where
  toEgison (x, y, z) = Tuple [toEgison x, toEgison y, toEgison z]
  fromEgison (Tuple [x, y, z]) = do
    x' <- fromEgison x
    y' <- fromEgison y
    z' <- fromEgison z
    return (x', y', z')
  fromEgison val = liftError $ throwError $ TypeMismatch "two elements tuple" (Value val)

instance (EgisonData a, EgisonData b, EgisonData c, EgisonData d) => EgisonData (a, b, c, d) where
  toEgison (x, y, z, w) = Tuple [toEgison x, toEgison y, toEgison z, toEgison w]
  fromEgison (Tuple [x, y, z, w]) = do
    x' <- fromEgison x
    y' <- fromEgison y
    z' <- fromEgison z
    w' <- fromEgison w
    return (x', y', z', w')
  fromEgison val = liftError $ throwError $ TypeMismatch "two elements tuple" (Value val)

fromCharValue :: EgisonValue -> Either EgisonError Char
fromCharValue (Char c) = return c
fromCharValue val = throwError $ TypeMismatch "char" (Value val)

fromStringValue :: EgisonValue -> Either EgisonError Text
fromStringValue (String str) = return str
fromStringValue val = throwError $ TypeMismatch "string" (Value val)

fromBoolValue :: EgisonValue -> Either EgisonError Bool
fromBoolValue (Bool b) = return b
fromBoolValue val = throwError $ TypeMismatch "bool" (Value val)

fromIntegerValue :: EgisonValue -> Either EgisonError Integer
fromIntegerValue (ScalarData (Div (Plus []) (Plus [Term 1 []]))) = return 0
fromIntegerValue (ScalarData (Div (Plus [Term x []]) (Plus [Term 1 []]))) = return x
fromIntegerValue val = throwError $ TypeMismatch "integer" (Value val)

fromRationalValue :: EgisonValue -> Either EgisonError Rational
fromRationalValue (ScalarData (Div (Plus []) _)) = return 0
fromRationalValue (ScalarData (Div (Plus [Term x []]) (Plus [Term y []]))) = return (x % y)
fromRationalValue val = throwError $ TypeMismatch "rational" (Value val)

fromFloatValue :: EgisonValue -> Either EgisonError Double
fromFloatValue (Float f 0) = return f
fromFloatValue val = throwError $ TypeMismatch "float" (Value val)

fromPortValue :: EgisonValue -> Either EgisonError Handle
fromPortValue (Port h) = return h
fromPortValue val = throwError $ TypeMismatch "port" (Value val)

--
-- Internal Data
--

-- |For memoization
type ObjectRef = IORef Object

data Object =
    Thunk (EgisonM WHNFData)
  | WHNF WHNFData

data WHNFData =
    Intermediate Intermediate
  | Value EgisonValue

data Intermediate =
    IInductiveData String [ObjectRef]
  | ITuple [ObjectRef]
  | ICollection (IORef (Seq Inner))
  | IArray (Array.Array Integer ObjectRef)
  | IIntHash (HashMap Integer ObjectRef)
  | ICharHash (HashMap Char ObjectRef)
  | IStrHash (HashMap Text ObjectRef)
  | ITensor (Tensor WHNFData)

data Inner =
    IElement ObjectRef
  | ISubCollection ObjectRef
    
instance Show WHNFData where
  show (Value val) = show val 
  show (Intermediate (IInductiveData name _)) = "<" ++ name ++ " ...>"
  show (Intermediate (ITuple _)) = "[...]"
  show (Intermediate (ICollection _)) = "{...}"
  show (Intermediate (IArray _)) = "(|...|)" 
  show (Intermediate (IIntHash _)) = "{|...|}" 
  show (Intermediate (ICharHash _)) = "{|...|}" 
  show (Intermediate (IStrHash _)) = "{|...|}" 
--  show (Intermediate (ITensor _)) = "[|...|]" 
  show (Intermediate (ITensor (Tensor ns xs _))) = "[|" ++ show (length ns) ++ show (V.length xs) ++ "|]" 

instance Show Object where
  show (Thunk _) = "#<thunk>"
  show (WHNF whnf) = show whnf

instance Show ObjectRef where
  show _ = "#<ref>"

--
-- Extract data from WHNF
--
class (EgisonData a) => EgisonWHNF a where
  toWHNF :: a -> WHNFData
  fromWHNF :: WHNFData -> EgisonM a
  toWHNF = Value . toEgison
  
instance EgisonWHNF Char where
  fromWHNF = liftError . fromCharWHNF
  
instance EgisonWHNF Text where
  fromWHNF = liftError . fromStringWHNF
  
instance EgisonWHNF Bool where
  fromWHNF = liftError . fromBoolWHNF
  
instance EgisonWHNF Integer where
  fromWHNF = liftError . fromIntegerWHNF
  
instance EgisonWHNF Double where
  fromWHNF = liftError . fromFloatWHNF
  
instance EgisonWHNF Handle where
  fromWHNF = liftError . fromPortWHNF
  
fromCharWHNF :: WHNFData -> Either EgisonError Char
fromCharWHNF (Value (Char c)) = return c
fromCharWHNF whnf = throwError $ TypeMismatch "char" whnf

fromStringWHNF :: WHNFData -> Either EgisonError Text
fromStringWHNF (Value (String str)) = return str
fromStringWHNF whnf = throwError $ TypeMismatch "string" whnf

fromBoolWHNF :: WHNFData -> Either EgisonError Bool
fromBoolWHNF (Value (Bool b)) = return b
fromBoolWHNF whnf = throwError $ TypeMismatch "bool" whnf

fromIntegerWHNF :: WHNFData -> Either EgisonError Integer
fromIntegerWHNF (Value (ScalarData (Div (Plus []) (Plus [Term 1 []])))) = return 0
fromIntegerWHNF (Value (ScalarData (Div (Plus [Term x []]) (Plus [Term 1 []])))) = return x
fromIntegerWHNF whnf = throwError $ TypeMismatch "integer" whnf

fromFloatWHNF :: WHNFData -> Either EgisonError Double
fromFloatWHNF (Value (Float f 0)) = return f
fromFloatWHNF whnf = throwError $ TypeMismatch "float" whnf

fromPortWHNF :: WHNFData -> Either EgisonError Handle
fromPortWHNF (Value (Port h)) = return h
fromPortWHNF whnf = throwError $ TypeMismatch "port" whnf

class (EgisonWHNF a) => EgisonObject a where
  toObject :: a -> Object
  toObject = WHNF . toWHNF
  
--
-- Environment
--

data Env = Env { envExpr::MS.Map Var ObjectRef, envType::[(Var, Type)], envImplConv::[(Type, Type, Expr)], envAbsImplConv::[(Type, Type, Expr)] ,envDisableTypecheck::[Var]}
 deriving (Show)

newtype Var = Var [String]
 deriving (Eq, Ord)

data VarWithIndexType = VarWithIndexType String [Index ()]
 deriving (Eq)
type Binding = (Var, ObjectRef)

data VarWithIndices = VarWithIndices String [Index String]
 deriving (Eq)

instance Show Var where
  show (Var xs) = intercalate "." xs

instance Show VarWithIndexType where
  show (VarWithIndexType x is) = x ++ concatMap show is

instance Show VarWithIndices where
  show (VarWithIndices x is) = x ++ concatMap show is

instance Show (Index ()) where
  show (Superscript ()) = "~"
  show (Subscript ()) = "_"
  show (SupSubscript ()) = "~_"
  show (DFscript _ _) = ""
  show (Userscript _) = "|"

instance Show (Index String) where
  show (Superscript s) = "~" ++ s
  show (Subscript s) = "_" ++ s
  show (SupSubscript s) = "~_" ++ s
  show (DFscript _ _) = ""
  show (Userscript i) = "|" ++ show i

instance Show (Index Expr) where
  show (Superscript i) = "~" ++ show i
  show (Subscript i) = "_" ++ show i
  show (SupSubscript i) = "~_" ++ show i
  show (DFscript _ _) = ""
  show (Userscript i) = "|" ++ show i

instance Show (Index ScalarData) where
  show (Superscript i) = "~" ++ show i
  show (Subscript i) = "_" ++ show i
  show (SupSubscript i) = "~_" ++ show i
  show (DFscript _ _) = ""
  show (Userscript i) = "|" ++ show i

instance Show (Index EgisonValue) where
  show (Superscript i) = case i of
                         ScalarData (Div (Plus [Term 1 [(Symbol id name (a:indices), 1)]]) (Plus [Term 1 []])) -> "~[" ++ show i ++ "]"
                         _ -> "~" ++ show i
  show (Subscript i) = case i of
                         ScalarData (Div (Plus [Term 1 [(Symbol id name (a:indices), 1)]]) (Plus [Term 1 []])) -> "_[" ++ show i ++ "]"
                         _ -> "_" ++ show i
  show (SupSubscript i) = "~_" ++ show i
  show (DFscript i j) = "_d" ++ show i ++ show j
  show (Userscript i) = case i of
                         ScalarData (Div (Plus [Term 1 [(Symbol id name (a:indices), 1)]]) (Plus [Term 1 []])) -> "_[" ++ show i ++ "]"
                         _ -> "|" ++ show i

nullEnv :: Env
nullEnv = Env { envExpr = MS.empty, envType = [], envImplConv = [], envAbsImplConv = [] ,envDisableTypecheck = []}

extendEnv :: Env -> [Binding] -> Env
extendEnv env bind = env { envExpr= foldr (\(k,v) -> MS.insert k v) (envExpr env) bind }

refVar :: Env -> Var -> Maybe ObjectRef
refVar env var = MS.lookup var $ envExpr env

extendEnvImplConv :: [(Type,Type,Expr)] -> Env -> Env
extendEnvImplConv is e = e { envImplConv=is++envImplConv e }

refEnvImplConv :: Env -> Type -> [(Type, Expr)]
refEnvImplConv e t = map (\(t1,t2,e) -> (t2,e)) $ filter (\(t1,_,_) -> t1 == t) $ envImplConv e

extendEnvAbsImplConv :: [(Type,Type,Expr)] -> Env -> Env
extendEnvAbsImplConv is e = e { envAbsImplConv=is++envAbsImplConv e }

refEnvAbsImplConv :: Env -> Type -> [(Type, Expr)]
refEnvAbsImplConv e t = map (\(t1,t2,e) -> (t2,e)) $ filter (\(t1,_,_) -> t1 == t) $ envAbsImplConv e

refEnvType :: Var -> Env -> Maybe Type
refEnvType v e = lookup v $ envType e

extendEnvType :: [(Var,Type)] -> Env -> Env
extendEnvType t e = e { envType = t ++ envType e }

deleteEnvType :: [Var] -> Env -> Env
deleteEnvType v e = e { envType = filter (\x -> not (fst x `elem` v)) $ envType e }


refEnvDisableTypecheck :: Var -> Env -> Bool
refEnvDisableTypecheck v e = v `elem` (envDisableTypecheck e)

extendEnvDisableTypecheck :: Var -> Env -> Env
extendEnvDisableTypecheck v e = e { envDisableTypecheck = v : envDisableTypecheck e }

--
-- Pattern Match
--

type Match = [Binding]

data PMMode = BFSMode | DFSMode
 deriving (Show)

pmMode :: Matcher -> PMMode
pmMode (UserMatcher _ mode _) = mode
pmMode (Tuple _) = DFSMode
pmMode Something = DFSMode

data MatchingState = MState Env [LoopPatContext] [Binding] [MatchingTree]
 deriving (Show)

data MatchingTree =
    MAtom EgisonPattern WHNFData Matcher
  | MNode [PatternBinding] MatchingState
 deriving (Show)

type PatternBinding = (String, EgisonPattern)

data LoopPatContext = LoopPatContext Binding ObjectRef EgisonPattern EgisonPattern EgisonPattern
 deriving (Show)

--
-- Errors
--

data EgisonError =
    UnboundVariable String
  | TypeMismatch String WHNFData
  | ArgumentsNumWithNames [String] Int Int
  | ArgumentsNumPrimitive Int Int
  | ArgumentsNum Int Int
  | InconsistentTensorSize
  | InconsistentTensorIndex
  | TensorIndexOutOfBounds Integer Integer
  | NotImplemented String
  | Assertion String
  | Match String
  | Parser String
  | Desugar String
  | EgisonBug String
  | Default String
  deriving Typeable
    
instance Show EgisonError where
  show (Parser err) = "Parse error at: " ++ err
  show (UnboundVariable var) = "Unbound variable: " ++ show var
  show (TypeMismatch expected found) = "Expected " ++  expected ++
                                        ", but found: " ++ show found
  show (ArgumentsNumWithNames names expected got) = "Wrong number of arguments: " ++ show names ++ ": expected " ++
                                                    show expected ++ ", but got " ++  show got
  show (ArgumentsNumPrimitive expected got) = "Wrong number of arguments for a primitive function: expected " ++
                                              show expected ++ ", but got " ++  show got
  show (ArgumentsNum expected got) = "Wrong number of arguments: expected " ++
                                      show expected ++ ", but got " ++  show got
  show InconsistentTensorSize = "Inconsistent tensor size"
  show InconsistentTensorIndex = "Inconsistent tensor index"
  show (TensorIndexOutOfBounds m n) = "Tensor index out of bounds: " ++ show m ++ ", " ++ show n
  show (NotImplemented message) = "Not implemented: " ++ message
  show (Assertion message) = "Assertion failed: " ++ message
  show (Desugar message) = "Error: " ++ message
  show (EgisonBug message) = "Egison Error: " ++ message
  show (Default message) = "Error: " ++ message

instance Exception EgisonError

liftError :: (MonadError e m) => Either e a -> m a
liftError = either throwError return

--
-- Monads
--

newtype EgisonM a = EgisonM {
    unEgisonM :: ExceptT EgisonError (FreshT IO) a
  } deriving (Functor, Applicative, Monad, MonadIO, MonadError EgisonError, MonadFresh)

parallelMapM :: (a -> EgisonM b) -> [a] -> EgisonM [b]
parallelMapM f [] = return []
parallelMapM f (x:xs) = do
    let y = unsafePerformEgison (0,1) $ f x
    let ys = unsafePerformEgison (0,1) $ parallelMapM f xs
    y `par` (ys `pseq` return (y:ys))

unsafePerformEgison :: (Int, Int) -> EgisonM a -> a
unsafePerformEgison (x, y) ma =
  let (Right ret, _) = unsafePerformIO $ runFreshT (x, y + 1) $ runEgisonM ma in
  ret
--    f' :: (Either EgisonError a) -> (Either EgisonError b) -> EgisonM c
--    f' (Right x) (Right y) = f x y
--    f' (Left e) _ = liftError (Left e)
--    f' _ (Left e) = liftError (Left e)

runEgisonM :: EgisonM a -> FreshT IO (Either EgisonError a)
runEgisonM = runExceptT . unEgisonM

liftEgisonM :: Fresh (Either EgisonError a) -> EgisonM a
liftEgisonM m = EgisonM $ ExceptT $ FreshT $ do
  s <- get
  (a, s') <- return $ runFresh s m
  put s'
  return $ either throwError return a   
  
fromEgisonM :: EgisonM a -> IO (Either EgisonError a)
fromEgisonM = modifyCounter . runEgisonM

counter :: IORef (Int, Int)
counter = unsafePerformIO (newIORef (0, 0))

readCounter :: IO (Int, Int)
readCounter = readIORef counter

updateCounter :: (Int, Int) -> IO ()
updateCounter = writeIORef counter

modifyCounter :: FreshT IO a -> IO a
modifyCounter m = do
  seed <- readCounter
  (result, seed) <- runFreshT seed m 
  updateCounter seed
  return result  

newtype FreshT m a = FreshT { unFreshT :: StateT (Int, Int) m a }
  deriving (Functor, Applicative, Monad, MonadState (Int, Int), MonadTrans)

type Fresh = FreshT Identity

class (Applicative m, Monad m) => MonadFresh m where
  fresh :: m String
  freshV :: m Var

instance (Applicative m, Monad m) => MonadFresh (FreshT m) where
  fresh = FreshT $ do (x, y) <- get; modify (\(x,y) -> (x + 1, y))
                      return $ "$_" ++ show x ++ show y
  freshV = FreshT $ do (x, y) <- get; modify (\(x,y) -> (x + 1, y))
                       return $ Var ["$_" ++ show x ++ show y]
instance (MonadError e m) => MonadError e (FreshT m) where
  throwError = lift . throwError
  catchError m h = FreshT $ catchError (unFreshT m) (unFreshT . h)

instance (MonadState s m) => MonadState s (FreshT m) where
  get = lift $ get
  put s = lift $ put s

instance (MonadFresh m) => MonadFresh (StateT s m) where
  fresh = lift $ fresh
  freshV = lift $ freshV

instance (MonadFresh m) => MonadFresh (ExceptT e m) where
  fresh = lift $ fresh
  freshV = lift $ freshV

instance (MonadFresh m, Monoid e) => MonadFresh (ReaderT e m) where
  fresh = lift $ fresh
  freshV = lift $ freshV

instance (MonadFresh m, Monoid e) => MonadFresh (WriterT e m) where
  fresh = lift $ fresh
  freshV = lift $ freshV

instance MonadIO (FreshT IO) where
  liftIO = lift

runFreshT :: Monad m => (Int, Int) -> FreshT m a -> m (a, (Int, Int))
runFreshT = flip (runStateT . unFreshT)

runFresh :: (Int, Int) -> Fresh a -> (a, (Int, Int))
runFresh seed m = runIdentity $ flip runStateT seed $ unFreshT m


type MatchM = MaybeT EgisonM

matchFail :: MatchM a
matchFail = MaybeT $ return Nothing

data MList m a = MNil | MCons a (m (MList m a))

instance Show (MList m a) where
  show MNil = "MNil"
  show (MCons _ _) = "(MCons ... ...)"

fromList :: Monad m => [a] -> MList m a
fromList = foldr f MNil
 where f x xs = MCons x $ return xs

fromSeq :: Monad m => Seq a -> MList m a
fromSeq = foldr f MNil
 where f x xs = MCons x $ return xs

fromMList :: Monad m => MList m a -> m [a]
fromMList = mfoldr f $ return []
  where f x xs = (x:) <$> xs

msingleton :: Monad m => a -> MList m a
msingleton = flip MCons $ return MNil

mfoldr :: Monad m => (a -> m b -> m b) -> m b -> MList m a -> m b
mfoldr f init MNil = init
mfoldr f init (MCons x xs) = f x (xs >>= mfoldr f init)

mappend :: Monad m => MList m a -> m (MList m a) -> m (MList m a)
mappend xs ys = mfoldr ((return .) . MCons) ys xs

mconcat :: Monad m => MList m (MList m a) -> m (MList m a)
mconcat = mfoldr mappend $ return MNil

mmap :: Monad m => (a -> m b) -> MList m a -> m (MList m b)
mmap f = mfoldr g $ return MNil
  where g x xs = f x >>= return . flip MCons xs

mfor :: Monad m => MList m a -> (a -> m b) -> m (MList m b)
mfor = flip mmap

-- Typing

isBool :: EgisonValue -> Bool
isBool (Bool _) = True
isBool _ = False

isBool' :: PrimitiveFunc
isBool' (Value val) = return $ Value $ Bool $ isBool val

isInteger :: EgisonValue -> Bool
isInteger (ScalarData (Div (Plus []) (Plus [Term 1 []]))) = True
isInteger (ScalarData (Div (Plus [Term _ []]) (Plus [Term 1 []]))) = True
isInteger _ = False

isInteger' :: PrimitiveFunc
isInteger' (Value val) = return $ Value $ Bool $ isInteger val

isRational :: EgisonValue -> Bool
isRational (ScalarData (Div (Plus []) (Plus [Term _ []]))) = True
isRational (ScalarData (Div (Plus [Term _ []]) (Plus [Term _ []]))) = True
isRational _ = False

isRational' :: PrimitiveFunc
isRational' (Value val) = return $ Value $ Bool $ isRational val

isSymbol :: EgisonValue -> Bool
isSymbol (ScalarData (Div (Plus [Term 1 [(Symbol _ _ _, 1)]]) (Plus [Term 1 []]))) = True
isSymbol _ = False

isScalar :: EgisonValue -> Bool
isScalar (ScalarData _) = True
isScalar _ = False

isScalar' :: PrimitiveFunc
isScalar' (Value val) = return $ Value $ Bool $ isScalar val
isScalar' _ = return $ Value $ Bool False

isTensor :: EgisonValue -> Bool
isTensor (TensorData _) = True
isTensor _ = False

isTensor' :: PrimitiveFunc
isTensor' (Value val) = return $ Value $ Bool $ isTensor val
isTensor' _ = return $ Value $ Bool False

isTensorWithIndex :: EgisonValue -> Bool
isTensorWithIndex (TensorData (Tensor _ _ (_:_))) = True
isTensorWithIndex _ = False

isTensorWithIndex' :: PrimitiveFunc
isTensorWithIndex' (Value val) = return $ Value $ Bool $ isTensorWithIndex val
isTensorWithIndex' _ = return $ Value $ Bool False

isFloat' :: PrimitiveFunc
isFloat' (Value (Float _ 0)) = return $ Value $ Bool True
isFloat' _ = return $ Value $ Bool False

isComplex' :: PrimitiveFunc
isComplex' (Value (Float _ _)) = return $ Value $ Bool True
isComplex' _ = return $ Value $ Bool False

isChar' :: PrimitiveFunc
isChar' (Value (Char _)) = return $ Value $ Bool True
isChar' _ = return $ Value $ Bool False

isString' :: PrimitiveFunc
isString' (Value (String _)) = return $ Value $ Bool True
isString' _ = return $ Value $ Bool False

isCollection' :: PrimitiveFunc
isCollection' (Value (Collection _)) = return $ Value $ Bool True
isCollection' (Intermediate (ICollection _)) = return $ Value $ Bool True
isCollection' _ = return $ Value $ Bool False

isArray' :: PrimitiveFunc
isArray' (Value (Array _)) = return $ Value $ Bool True
isArray' (Intermediate (IArray _)) = return $ Value $ Bool True
isArray' _ = return $ Value $ Bool False

isHash' :: PrimitiveFunc
isHash' (Value (IntHash _)) = return $ Value $ Bool True
isHash' (Value (StrHash _)) = return $ Value $ Bool True
isHash' (Intermediate (IIntHash _)) = return $ Value $ Bool True
isHash' (Intermediate (IStrHash _)) = return $ Value $ Bool True
isHash' _ = return $ Value $ Bool False

readUTF8File :: FilePath -> IO String
readUTF8File name = do
  h <- openFile name ReadMode
  hSetEncoding h utf8
  hGetContents h

stringToVar :: String -> Var
stringToVar name = Var $ splitOn "." name
