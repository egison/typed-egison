{- |
Module      : Language.Egison.Types
Copyright   : Akira Kawata
Licence     : MIT

This module contains static type checking algorithm for Egison
I suggest you to import this file using qualified import.
-}

module Language.Egison.TypeCheck where

import qualified Language.Egison.Types as ET
import Control.Monad.State (State,evalState,get,put)
import Control.Monad.Trans.Except (ExceptT,runExceptT,catchE)
import Control.Monad.Except(throwError)
import Data.Maybe (fromMaybe)
import Data.List(nub)

-- TStar is a kind of wildcard of type.
-- The argument of TFun is Tuple.
-- This is because Egison doesn't do currying, so the arity doesn't change.
-- TCollection is like a list in Haskell.
-- All its element must have the same type.
-- TCFun a b is a function which have arbitrary length args like (+ 1 2 3 4).
-- All TCFun arguments have same type a.
data Type = TChar | TString | TBool | TInt | TVar TVarIndex | TStar |
            TFun Type Type | TTuple [Type] | TCollection Type | TPattern Type | TMatcher Type
            deriving (Show,Eq)
type TVarIndex = Int

-- First element of Restriction will be type valiable.
-- Second element of Restriction is what the first element refer.
type Restriction = (Type,Type) 
type Substitution = [Restriction]
-- [(Variable name, Type)]
type TypeEnvironment = [([String],Type)]
type MakeSubstition = ExceptT String (State TVarIndex)

checkTopExpr :: ET.EgisonTopExpr -> Either String (Substitution, Type)
checkTopExpr (ET.Test e) = exprToSub e
checkTopExpr _ = return ([], TStar)

exprToSub :: ET.EgisonExpr -> Either String (Substitution, Type)
exprToSub e = evalState (runExceptT $ exprToSub' [] (TVar 0) e) 1

applySub :: Substitution -> Type -> Type
applySub s (TVar i) = fromMaybe (TVar i) (lookup (TVar i) s)
applySub s (TFun t1 t2) = TFun (applySub s t1) (applySub s t2)
applySub s (TTuple ts) = TTuple (map (applySub s) ts)
applySub s (TCollection t) = TCollection (applySub s t)
applySub s (TPattern t) = TPattern (applySub s t)
applySub s (TMatcher t) = TMatcher (applySub s t)
applySub _ t = t

freeTVarIndex :: Type -> [TVarIndex]
freeTVarIndex = nub . freeTVarIndex'
    where
        freeTVarIndex' (TVar i) = [i]
        freeTVarIndex' (TFun t1 t2) = freeTVarIndex' t1 ++ freeTVarIndex' t2
        freeTVarIndex' (TTuple ts) = concatMap freeTVarIndex' ts
        freeTVarIndex' (TCollection t1) = freeTVarIndex' t1
        freeTVarIndex' (TPattern t1) = freeTVarIndex' t1
        freeTVarIndex' (TMatcher t1) = freeTVarIndex' t1
        freeTVarIndex' _ = []

-- replace all t1 in t3 with t2
replace :: Type -> Type -> Type -> Type
replace t1 t2 t3 = if t1 == t3
  then t2
  else case t3 of
    TFun t4 t5 -> TFun (replace t1 t2 t4) (replace t1 t2 t5)
    TTuple ts -> TTuple (map (replace t1 t2) ts)
    TCollection t -> TCollection (replace t1 t2 t)
    TPattern t -> TPattern (replace t1 t2 t)
    TMatcher t -> TMatcher (replace t1 t2 t)
    _ -> t3

-- replace all t1 in s with t2
replaceSubstituition :: Type -> Type -> Substitution -> Substitution
replaceSubstituition t1 t2 s = map (\(x,y) -> ((replace t1 t2 x), (replace t1 t2 y))) s

unifySub :: Substitution -> MakeSubstition Substitution
unifySub [] = return []
unifySub ((t1, t2) : r)
    | t1 == t2 = unifySub r
    | otherwise = case (t1, t2) of
        ((TFun t3 t4),(TFun t5 t6)) -> unifySub ((t3,t5):(t4,t6):r)
        (TTuple ts1, TTuple ts2) -> if length ts1 == length ts2
          then unifySub $ (zip ts1 ts2) ++ r
          else throwError "Lengths of tuple are not equal"
        (TCollection t3,TCollection t4) -> unifySub $ (t3,t4):r
        (TPattern t3,TPattern t4) -> unifySub $ (t3,t4):r
        (TMatcher t3,TMatcher t4) -> unifySub $ (t3,t4):r
        (TVar tv1,t4) -> if tv1 `elem` freeTVarIndex t4
            then throwError "Type variable is occured recursively."
            else do
              u <- unifySub (replaceSubstituition (TVar tv1) t4 r) 
              return $ ((applySub u (TVar tv1)),(applySub u t4)):u
        (t4, TVar t3) -> unifySub ((TVar t3,t4) : r)
        (TStar, _) -> unifySub r
        (_, TStar) -> unifySub r
        otherwise -> throwError $ "Undefined pattern in unifySub " ++ show (t1,t2)


getNewTVarIndex :: MakeSubstition TVarIndex
getNewTVarIndex = do
  i <-get
  put (i+1)
  return i

innersToExprs :: [ET.InnerExpr] -> [ET.EgisonExpr]
innersToExprs [] = []
innersToExprs (ET.ElementExpr e:rest) = e:(innersToExprs rest)
innersToExprs ((ET.SubCollectionExpr (ET.CollectionExpr is)):rest) =
    innersToExprs is ++ innersToExprs rest

removeTensorMap :: ET.EgisonExpr -> ET.EgisonExpr
removeTensorMap (ET.TensorMapExpr (ET.LambdaExpr _ b) _) = removeTensorMap b
removeTensorMap (ET.TensorMap2Expr (ET.LambdaExpr _ b) _ _) = removeTensorMap b
removeTensorMap e = e

lookupTypeEnv :: [String] -> TypeEnvironment -> MakeSubstition Type
lookupTypeEnv e [] = do
  i <- getNewTVarIndex
  return $ (TVar i)
lookupTypeEnv e1 ((e2,t):r)
  | e1 == e2 = return t
  | otherwise = lookupTypeEnv e1 r

patternToSub :: TypeEnvironment -> Type -> ET.EgisonPattern -> MakeSubstition (Substitution, Type)
patternToSub _ _ _ = return ([], TStar)

exprToSub' :: TypeEnvironment -> Type -> ET.EgisonExpr -> MakeSubstition (Substitution, Type)
exprToSub' env ty (ET.CharExpr _ ) = return ([(ty,TChar)], TChar)
exprToSub' env ty (ET.StringExpr _) = return ([(ty,TString)], TString)
exprToSub' env ty (ET.BoolExpr _) = return ([(ty,TBool)], TBool)
exprToSub' env ty (ET.IntegerExpr _) = return ([(ty,TInt)], TInt)
exprToSub' env ty (ET.VarExpr (ET.Var vn)) = do
    ty' <- lookupTypeEnv vn env
    sub <- unifySub [(ty',ty)]
    return (sub, applySub sub ty')
exprToSub' env ty (ET.IfExpr e1 e2 e3) = do
    let cb = (\x -> throwError "The condition of if expression is not Bool")
    let ct = (\x -> throwError "The two type of bodies of if expression do not correspond.")
    (sub1, t1) <- exprToSub' env TBool e1
    (sub2, t2) <- exprToSub' env ty e2
    (sub3, t3) <- exprToSub' env ty e3
    sub4 <- catchE (unifySub $ (t1, TBool) : sub1) cb
    sub5 <- catchE (unifySub $ (t2, t3) : sub4 ++ sub2 ++ sub3) ct
    return (sub5, applySub sub5 t2)
exprToSub' env ty (ET.TupleExpr es) = do
    sts <- mapM (exprToSub' env TStar) es
    let ty' = TTuple (map snd sts)
    sub <- unifySub $ (ty, ty') : (foldr (++) [] (map fst sts))
    return (sub, applySub sub ty')
exprToSub' env ty (ET.CollectionExpr es) = do
    let es' = innersToExprs es
    sts <- mapM (exprToSub' env TStar) es'
    let sub1 = foldr (++) [] (map fst sts)
    tv <- getNewTVarIndex
    let sub2 = map (\x -> (TVar tv, snd x)) sts
    let ty' = TCollection (TVar tv)
    let cc = (\x -> throwError "The elemtents of collection do not have the same type.")
    sub3 <- catchE (unifySub $ ((ty, ty') : sub1 ++ sub2)) cc
    return (sub3, applySub sub3 ty')
exprToSub' env ty (ET.LambdaExpr args body) = do
    let args1 = filter (/= []) $ map f args
    let body1 = removeTensorMap body
    arg1tys <- mapM (\_ -> do { x <- getNewTVarIndex; return (TVar x)}) args1
    let env1 = (zip args1 arg1tys) ++ env
    tv <- getNewTVarIndex
    (sub1,ty1) <- exprToSub' env1 (TVar tv) body1
    sub2 <- unifySub $ (ty, TFun (TTuple arg1tys) ty1):sub1
    return (sub2, applySub sub2 ty)
      where f (ET.TensorArg s) = [s]
            f _ = []
exprToSub' env ty (ET.ApplyExpr fun arg) = do
    tv <- getNewTVarIndex
    (sub1, t1) <- exprToSub' env (TVar tv) arg
    (sub2, t2) <- exprToSub' env (TFun (TVar tv) ty) fun
    let cc = (\x -> throwError "Wrong arguments are passed to a function.")
    sub3 <- catchE (unifySub $ (t2, (TFun (TVar tv) ty)) : (t1, TVar tv) : sub1 ++ sub2) cc
    return (sub3, applySub sub3 ty)
exprToSub' env ty (ET.LetExpr binds body) = do
    let names = filter (/= []) $ map f binds
    let exs = map snd binds
    tys <- mapM (\x -> getNewTVarIndex >>= (return . TVar)) binds
    sts <- mapM (\(x,y) -> exprToSub' env x y) $ zip tys exs
    let env1 = env ++ zip names tys
    let sub1 = zip tys (map snd sts) ++ foldr (++) [] (map fst sts)
    sub2 <- unifySub sub1
    (sub3, ty3) <- exprToSub' env1 ty body
    sub4 <- unifySub $ sub2 ++ sub3
    return (sub4, applySub sub4 ty)
      where f (([ET.Var s],_)) = s
            f _ = []
exprToSub' env ty (ET.LetRecExpr binds body) = do
    let names = filter (/= []) $ map f binds
    let exs = map snd binds
    tys <- mapM (\x -> getNewTVarIndex >>= (return . TVar)) binds
    sts <- mapM (\(x,y) -> exprToSub' env x y) $ zip tys exs
    let env1 = env ++ zip names tys
    let sub1 = zip tys (map snd sts) ++ foldr (++) [] (map fst sts)
    sub2 <- unifySub sub1
    (sub3, ty3) <- exprToSub' env1 ty body
    sub4 <- unifySub $ sub2 ++ sub3
    return (sub4, applySub sub4 ty)
      where f (([ET.Var s],_)) = s
            f _ = []
exprToSub' env ty (ET.MatchAllExpr dt mt (pt,ex)) = do
    tvdt <- getNewTVarIndex
    tvex <- getNewTVarIndex
    (sub1, ty1) <- exprToSub' env (TVar tvdt) dt
    (sub2, ty2) <- exprToSub' env (TMatcher (TVar tvdt)) mt
    (sub3, ty3) <- patternToSub env (TPattern (TVar tvdt)) pt
    (sub4, ty4) <- exprToSub' env (TVar tvex) ex
    sub5 <- unifySub $ (ty1, TVar tvdt) : (ty2,TMatcher (TVar tvdt)) : (ty4, TVar tvex) : (ty,TCollection (TVar tvex)) : sub1 ++ sub2 ++ sub4
    return (sub5, applySub sub5 ty)
exprToSub' env ty _ = return ([], TStar)

