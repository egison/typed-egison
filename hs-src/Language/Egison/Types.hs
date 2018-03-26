{- |
Module      : Language.Egison.Types
Copyright   : Akira Kawata
Licence     : MIT

This module contains static type checking algorithm for Egison
I suggest you to import this file using qualified import.
-}

module Language.Egison.Types where

import qualified Language.Egison.Expressions as EE
import Language.Egison.Expressions (Type(..), TypeVarIndex)
import Control.Monad.State (State,evalState,get,put)
import Control.Monad.Trans.Except (ExceptT,runExceptT,catchE)
import Control.Monad.Except(throwError)
import Data.Maybe (fromMaybe)
import Data.List(nub)

-- First element of Restriction will be type valiable.
-- Second element of Restriction is what the first element refer.
type Restriction = (Type,Type) 
type Substitution = [Restriction]
-- [(Variable name, Type)]
type TypeEnvironment = [([String],Type)]
type MakeSubstition = ExceptT String (State TypeVarIndex)

checkTopExpr :: EE.EgisonTopExpr -> Either String (Substitution, Type)
checkTopExpr (EE.Test e) = exprToSub e
checkTopExpr _ = return ([], TypeStar)

exprToSub :: EE.EgisonExpr -> Either String (Substitution, Type)
exprToSub e = evalState (runExceptT $ exprToSub' [] (TypeVar 0) e) 1

applySub :: Substitution -> Type -> Type
applySub s (TypeVar i) = fromMaybe (TypeVar i) (lookup (TypeVar i) s)
applySub s (TypeFun t1 t2) = TypeFun (applySub s t1) (applySub s t2)
applySub s (TypeTuple ts) = TypeTuple (map (applySub s) ts)
applySub s (TypeCollection t) = TypeCollection (applySub s t)
applySub s (TypePattern t) = TypePattern (applySub s t)
applySub s (TypeMatcher t) = TypeMatcher (applySub s t)
applySub _ t = t

freeTypeVarIndex :: Type -> [TypeVarIndex]
freeTypeVarIndex = nub . freeTypeVarIndex'
    where
        freeTypeVarIndex' (TypeVar i) = [i]
        freeTypeVarIndex' (TypeFun t1 t2) = freeTypeVarIndex' t1 ++ freeTypeVarIndex' t2
        freeTypeVarIndex' (TypeTuple ts) = concatMap freeTypeVarIndex' ts
        freeTypeVarIndex' (TypeCollection t1) = freeTypeVarIndex' t1
        freeTypeVarIndex' (TypePattern t1) = freeTypeVarIndex' t1
        freeTypeVarIndex' (TypeMatcher t1) = freeTypeVarIndex' t1
        freeTypeVarIndex' _ = []

-- replace all t1 in t3 with t2
replace :: Type -> Type -> Type -> Type
replace t1 t2 t3 = if t1 == t3
  then t2
  else case t3 of
    TypeFun t4 t5 -> TypeFun (replace t1 t2 t4) (replace t1 t2 t5)
    TypeTuple ts -> TypeTuple (map (replace t1 t2) ts)
    TypeCollection t -> TypeCollection (replace t1 t2 t)
    TypePattern t -> TypePattern (replace t1 t2 t)
    TypeMatcher t -> TypeMatcher (replace t1 t2 t)
    _ -> t3

-- replace all t1 in s with t2
replaceSubstituition :: Type -> Type -> Substitution -> Substitution
replaceSubstituition t1 t2 s = map (\(x,y) -> ((replace t1 t2 x), (replace t1 t2 y))) s

unifySub :: Substitution -> MakeSubstition Substitution
unifySub [] = return []
unifySub ((t1, t2) : r)
    | t1 == t2 = unifySub r
    | otherwise = case (t1, t2) of
        ((TypeFun t3 t4),(TypeFun t5 t6)) -> unifySub ((t3,t5):(t4,t6):r)
        (TypeTuple ts1, TypeTuple ts2) -> if length ts1 == length ts2
          then unifySub $ (zip ts1 ts2) ++ r
          else throwError "Lengths of tuple are not equal"
        (TypeCollection t3,TypeCollection t4) -> unifySub $ (t3,t4):r
        (TypePattern t3,TypePattern t4) -> unifySub $ (t3,t4):r
        (TypeMatcher t3,TypeMatcher t4) -> unifySub $ (t3,t4):r
        (TypeVar tv1,t4) -> if tv1 `elem` freeTypeVarIndex t4
            then throwError "Type variable is occured recursively."
            else do
              u <- unifySub (replaceSubstituition (TypeVar tv1) t4 r) 
              return $ ((applySub u (TypeVar tv1)),(applySub u t4)):u
        (t4, TypeVar t3) -> unifySub ((TypeVar t3,t4) : r)
        (TypeStar, _) -> unifySub r
        (_, TypeStar) -> unifySub r
        otherwise -> throwError $ "Undefined pattern in unifySub " ++ show (t1,t2)


getNewTypeVarIndex :: MakeSubstition TypeVarIndex
getNewTypeVarIndex = do
  i <-get
  put (i+1)
  return i

innersToExprs :: [EE.InnerExpr] -> [EE.EgisonExpr]
innersToExprs [] = []
innersToExprs (EE.ElementExpr e:rest) = e:(innersToExprs rest)
innersToExprs ((EE.SubCollectionExpr (EE.CollectionExpr is)):rest) =
    innersToExprs is ++ innersToExprs rest

removeTensorMap :: EE.EgisonExpr -> EE.EgisonExpr
removeTensorMap (EE.TensorMapExpr (EE.LambdaExpr _ b) _) = removeTensorMap b
removeTensorMap (EE.TensorMap2Expr (EE.LambdaExpr _ b) _ _) = removeTensorMap b
removeTensorMap e = e

lookupTypeEnv :: [String] -> TypeEnvironment -> MakeSubstition Type
lookupTypeEnv e [] = do
  i <- getNewTypeVarIndex
  return $ (TypeVar i)
lookupTypeEnv e1 ((e2,t):r)
  | e1 == e2 = return t
  | otherwise = lookupTypeEnv e1 r

patternToSub :: TypeEnvironment -> Type -> EE.EgisonPattern -> MakeSubstition (Substitution, Type)
patternToSub _ _ _ = return ([], TypeStar)

exprToSub' :: TypeEnvironment -> Type -> EE.EgisonExpr -> MakeSubstition (Substitution, Type)
exprToSub' env ty (EE.CharExpr _ ) = return ([(ty,TypeChar)], TypeChar)
exprToSub' env ty (EE.StringExpr _) = return ([(ty,TypeString)], TypeString)
exprToSub' env ty (EE.BoolExpr _) = return ([(ty,TypeBool)], TypeBool)
exprToSub' env ty (EE.IntegerExpr _) = return ([(ty,TypeInt)], TypeInt)
exprToSub' env ty (EE.VarExpr (EE.Var vn)) = do
    ty' <- lookupTypeEnv vn env
    sub <- unifySub [(ty',ty)]
    return (sub, applySub sub ty')
exprToSub' env ty (EE.IfExpr e1 e2 e3) = do
    let cb = (\x -> throwError "The condition of if expression is not Bool")
    let ct = (\x -> throwError "The two type of bodies of if expression do not correspond.")
    (sub1, t1) <- exprToSub' env TypeBool e1
    (sub2, t2) <- exprToSub' env ty e2
    (sub3, t3) <- exprToSub' env ty e3
    sub4 <- catchE (unifySub $ (t1, TypeBool) : sub1) cb
    sub5 <- catchE (unifySub $ (t2, t3) : sub4 ++ sub2 ++ sub3) ct
    return (sub5, applySub sub5 t2)
exprToSub' env ty (EE.TupleExpr es) = do
    sts <- mapM (exprToSub' env TypeStar) es
    let ty' = TypeTuple (map snd sts)
    sub <- unifySub $ (ty, ty') : (foldr (++) [] (map fst sts))
    return (sub, applySub sub ty')
exprToSub' env ty (EE.CollectionExpr es) = do
    let es' = innersToExprs es
    sts <- mapM (exprToSub' env TypeStar) es'
    let sub1 = foldr (++) [] (map fst sts)
    tv <- getNewTypeVarIndex
    let sub2 = map (\x -> (TypeVar tv, snd x)) sts
    let ty' = TypeCollection (TypeVar tv)
    let cc = (\x -> throwError "The elemtents of collection do not have the same type.")
    sub3 <- catchE (unifySub $ ((ty, ty') : sub1 ++ sub2)) cc
    return (sub3, applySub sub3 ty')
exprToSub' env ty (EE.LambdaExpr args body) = do
    let args1 = filter (/= []) $ map f args
    let body1 = removeTensorMap body
    arg1tys <- mapM (\_ -> do { x <- getNewTypeVarIndex; return (TypeVar x)}) args1
    let env1 = (zip args1 arg1tys) ++ env
    tv <- getNewTypeVarIndex
    (sub1,ty1) <- exprToSub' env1 (TypeVar tv) body1
    sub2 <- unifySub $ (ty, TypeFun (TypeTuple arg1tys) ty1):sub1
    return (sub2, applySub sub2 ty)
      where f (EE.TensorArg s) = [s]
            f _ = []
exprToSub' env ty (EE.ApplyExpr fun arg) = do
    tv <- getNewTypeVarIndex
    (sub1, t1) <- exprToSub' env (TypeVar tv) arg
    (sub2, t2) <- exprToSub' env (TypeFun (TypeVar tv) ty) fun
    let cc = (\x -> throwError "Wrong arguments are passed to a function.")
    sub3 <- catchE (unifySub $ (t2, (TypeFun (TypeVar tv) ty)) : (t1, TypeVar tv) : sub1 ++ sub2) cc
    return (sub3, applySub sub3 ty)
exprToSub' env ty (EE.LetExpr binds body) = do
    let names = filter (/= []) $ map f binds
    let exs = map snd binds
    tys <- mapM (\x -> getNewTypeVarIndex >>= (return . TypeVar)) binds
    sts <- mapM (\(x,y) -> exprToSub' env x y) $ zip tys exs
    let env1 = env ++ zip names tys
    let sub1 = zip tys (map snd sts) ++ foldr (++) [] (map fst sts)
    sub2 <- unifySub sub1
    (sub3, ty3) <- exprToSub' env1 ty body
    sub4 <- unifySub $ sub2 ++ sub3
    return (sub4, applySub sub4 ty)
      where f (([EE.Var s],_)) = s
            f _ = []
exprToSub' env ty (EE.LetRecExpr binds body) = do
    let names = filter (/= []) $ map f binds
    let exs = map snd binds
    tys <- mapM (\x -> getNewTypeVarIndex >>= (return . TypeVar)) binds
    sts <- mapM (\(x,y) -> exprToSub' env x y) $ zip tys exs
    let env1 = env ++ zip names tys
    let sub1 = zip tys (map snd sts) ++ foldr (++) [] (map fst sts)
    sub2 <- unifySub sub1
    (sub3, ty3) <- exprToSub' env1 ty body
    sub4 <- unifySub $ sub2 ++ sub3
    return (sub4, applySub sub4 ty)
      where f (([EE.Var s],_)) = s
            f _ = []
exprToSub' env ty (EE.MatchAllExpr dt mt (pt,ex)) = do
    tvdt <- getNewTypeVarIndex
    tvex <- getNewTypeVarIndex
    (sub1, ty1) <- exprToSub' env (TypeVar tvdt) dt
    (sub2, ty2) <- exprToSub' env (TypeMatcher (TypeVar tvdt)) mt
    (sub3, ty3) <- patternToSub env (TypePattern (TypeVar tvdt)) pt
    (sub4, ty4) <- exprToSub' env (TypeVar tvex) ex
    sub5 <- unifySub $ (ty1, TypeVar tvdt) : (ty2,TypeMatcher (TypeVar tvdt)) : (ty4, TypeVar tvex) : (ty,TypeCollection (TypeVar tvex)) : sub1 ++ sub2 ++ sub4
    return (sub5, applySub sub5 ty)
exprToSub' env ty _ = return ([], TypeStar)

