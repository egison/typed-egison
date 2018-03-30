{- |
Module      : Language.Egison.Types
Copyright   : Akira KAWATA
Licence     : MIT

This module contains static type checking algorithm for Egison
I suggest you to import this file using qualified import.
-}

module Language.Egison.Types(
  innersToExprs
  , checkTopExpr
  )where

import qualified Language.Egison.Expressions as EE
import Language.Egison.Expressions (Type(..), TypeVarIndex)
import Control.Monad.State (State,evalState,get,put,runState)
import Control.Monad.Trans.Except (ExceptT,runExceptT,catchE)
import Control.Monad.Except(throwError)
import Data.Maybe (fromMaybe)
import Data.List (nub)
import Debug.Trace
import Data.IORef (newIORef, readIORef, writeIORef, IORef)
import System.IO.Unsafe (unsafePerformIO)

-- First element of Restriction will be type valiable.
-- Second element of Restriction is what the first element refer.
data TypeScheme = TypeScheme [TypeVarIndex] Type deriving Show
type Restriction = (Type,Type)
type Substitution = [Restriction]
-- [(Variable name, Type)]
type TypeSchemeEnvironment = [(EE.Var,TypeScheme)]
type MakeSubstitionM = ExceptT String (State TypeVarIndex)

checkTopExpr :: EE.Env -> EE.TopExpr -> Either String (Substitution, Type)
checkTopExpr env (EE.Test e) = exprToSub env e
checkTopExpr env _ = return ([], TypeStar)

typeVarIndexCache :: IORef TypeVarIndex
typeVarIndexCache = unsafePerformIO $ newIORef 1

exprToSub :: EE.Env -> EE.Expr -> Either String (Substitution, Type)
exprToSub env exp = unsafePerformIO $ exprToSubIO env exp

exprToSubIO :: EE.Env -> EE.Expr -> IO (Either String (Substitution, Type))
exprToSubIO env exp = do
  i <- readIORef typeVarIndexCache
  let (a,s) = runState (runExceptT $ exprToSub' env1 (TypeVar 0) exp) i
  writeIORef typeVarIndexCache (s+1)
  return a
  where ty2tys ty = TypeScheme (freeTypeVarIndex ty) ty
        env1 = map (\(v,t) -> (v,ty2tys t)) (EE.envType env)

typeToTypeScheme :: TypeSchemeEnvironment -> Type -> TypeScheme
typeToTypeScheme env ty = TypeScheme (freeTypeVarIndex ty) ty
  where env2tvis [] = []
        env2tvis ((_,ts):rest) = freetvis ts ++ env2tvis rest
        freetvis (TypeScheme is t) = filter (\x -> not $ x `elem` is) $ freeTypeVarIndex t 

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

unifySub :: Substitution -> MakeSubstitionM Substitution
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


getNewTypeVar :: MakeSubstitionM Type
getNewTypeVar = do
  i <- get
  put (i+1)
  return $ TypeVar i

innersToExprs :: [EE.InnerExpr] -> [EE.Expr]
innersToExprs [] = []
innersToExprs (EE.ElementExpr e:rest) = e:(innersToExprs rest)
innersToExprs ((EE.SubCollectionExpr (EE.CollectionExpr is)):rest) =
    innersToExprs is ++ innersToExprs rest

lookupTypeSchemeEnv :: EE.Var -> TypeSchemeEnvironment -> MakeSubstitionM TypeScheme
lookupTypeSchemeEnv e [] = throwError $ "Cannot decide the type of " ++ show e
lookupTypeSchemeEnv e1 ((e2,t):r)
  | e1 == e2 = return t
  | otherwise = lookupTypeSchemeEnv e1 r

instantiateTypeScheme :: TypeScheme -> MakeSubstitionM Type
instantiateTypeScheme (TypeScheme tvis ty) = do
  sub <- mapM (\x -> (do
    t <- getNewTypeVar
    return (TypeVar x, t))) tvis
  return $ applySub sub ty


-- There is TypeEnvironment in return value. 
-- This is because new variables in pattern can be used in return expression.
-- For example, look following Egison program.
-- (match-all {1 2 3} (list integer) [<cons $x $xs> [x xs]])
-- $x and $xs is used in [x xs].
-- So we must bind all new variables($x,$xs) in the pattern to the environment.
patternToSub :: TypeSchemeEnvironment -> Type -> EE.EgisonPattern -> MakeSubstitionM (Substitution, TypeSchemeEnvironment, Type)
patternToSub env (TypePattern ty) (EE.ValuePat exp) = do
  (sub1, ty1) <- exprToSub' env ty exp
  sub2 <- unifySub $ (ty,ty1) : sub1
  return (sub2, env, applySub sub2 (TypePattern ty1))
patternToSub env (TypePattern ty) (EE.PatVar var) = do
  tv <- getNewTypeVar
  let env1 = (var,TypeScheme [] tv) : env
  let sub = [(ty, tv)]
  return (sub, env1, applySub sub (TypePattern ty))
patternToSub env (TypePattern ty) (EE.InductivePat pc pats) = do
  pctype <- lookupTypeSchemeEnv (EE.Var [pc]) env >>= instantiateTypeScheme
  (sub1, env1, tys1) <- f env pats
  sub2 <- unifySub $ (pctype, TypeFun (TypeTuple tys1) (TypePattern ty)) : sub1
  return (sub2, env1, applySub sub2 (TypePattern ty))
  where
    f :: TypeSchemeEnvironment -> [EE.EgisonPattern] -> MakeSubstitionM (Substitution, TypeSchemeEnvironment, [Type])
    f env [] = return ([], env, [])
    f env (p:rest) = do
      ty1 <- getNewTypeVar
      (sub2,env2,ty2) <- patternToSub env (TypePattern ty1) p
      (sub3,env3,tys3) <- f env2 rest
      return ((TypePattern ty1,ty2) : sub3, env3, ty2:tys3)
patternToSub _ (TypePattern _) _ = return ([], [], TypeStar)
patternToSub _ ty _ = throwError $ "Pattern is type as no pattern type " ++ show ty

exprToSub' :: TypeSchemeEnvironment -> Type -> EE.Expr -> MakeSubstitionM (Substitution, Type)
exprToSub' env ty (EE.CharExpr _ ) = return ([(ty,TypeChar)], TypeChar)
exprToSub' env ty (EE.StringExpr _) = return ([(ty,TypeString)], TypeString)
exprToSub' env ty (EE.BoolExpr _) = return ([(ty,TypeBool)], TypeBool)
exprToSub' env ty (EE.IntegerExpr _) = return ([(ty,TypeInt)], TypeInt)
exprToSub' env ty (EE.VarExpr vn) = do
    ty' <- lookupTypeSchemeEnv vn env >>= instantiateTypeScheme
    sub <- unifySub [(trace ("vn = " ++ show vn ++ " ty' = " ++ show ty') ty',ty)]
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
    tvs <- mapM (\x -> getNewTypeVar) es
    sts <- mapM (\(e,tv) -> exprToSub' env tv e) $ zip es tvs
    let ty1 = TypeTuple (map snd sts)
    sub <- unifySub $ (ty, ty1) : (ty,TypeTuple tvs) : (foldr (++) [] (map fst sts))
    return (sub, applySub sub ty1)
exprToSub' env ty (EE.CollectionExpr es) = do
    ty1 <- getNewTypeVar
    let es' = innersToExprs es
    sts <- mapM (exprToSub' env ty1) es'
    let sub1 = foldr (++) [] (map fst sts)
    ty2 <- getNewTypeVar
    let sub2 = map (\x -> (ty2, snd x)) sts
    let cc = (\x -> throwError "The elemtents of collection do not have the same type.")
    sub3 <- catchE (unifySub $ ((ty, TypeCollection ty2) : (ty, TypeCollection ty1) : sub1 ++ sub2)) cc
    return (sub3, applySub sub3 (TypeCollection ty2))
exprToSub' env ty (EE.LambdaExpr args body) = do
    let args1 = filter (/= EE.Var []) $ map f args
    arg1tys <- mapM (\_ -> getNewTypeVar) args1
    let env1 = (zip args1 (map (\x -> TypeScheme [] x) arg1tys)) ++ filter (\(v,_) -> not (v `elem` args1)) env
    tv <- getNewTypeVar
    (sub1,ty1) <- exprToSub' env1 tv body
    sub2 <- unifySub $ (ty, TypeFun (TypeTuple arg1tys) ty1):sub1
    return (sub2, applySub sub2 ty)
      where f (EE.TensorArg s) = EE.Var [s]
            f _ = EE.Var []
exprToSub' env ty (EE.ApplyExpr fun arg) = do
    tv <- getNewTypeVar
    (sub1, t1) <- exprToSub' env tv arg
    (sub2, t2) <- exprToSub' env (TypeFun tv ty) fun
    let cc = (\x -> throwError "Wrong arguments are passed to a function.")
    sub3 <- catchE (unifySub $ (t2, (TypeFun tv ty)) : (t1, tv) : sub1 ++ sub2) cc
    return (sub3, applySub sub3 ty)
exprToSub' env ty (EE.LetExpr binds body) = do
    let names = filter (/= EE.Var []) $ map f binds
    let exs = map snd binds
    tys <- mapM (\x -> getNewTypeVar) binds
    sts <- mapM (\(x,y) -> exprToSub' env x y) $ zip tys exs
    let tyshs = map (typeToTypeScheme env . snd) sts
    let env1 = filter (\(v,_) -> not (v `elem` names)) env ++ zip names tyshs
    let sub1 = zip tys (map snd sts) ++ foldr (++) [] (map fst sts)
    sub2 <- unifySub sub1
    (sub3, ty3) <- exprToSub' (trace ("env1 = " ++ show env1) env1) ty body
    sub4 <- unifySub $ sub2 ++ sub3
    return (sub4, applySub sub4 ty)
      where f (([EE.Var s],_)) = EE.Var s
            f _ = EE.Var []
exprToSub' env ty (EE.LetRecExpr binds body) = do
    let names = filter (/= EE.Var []) $ map f binds
    let exs = map snd binds
    tys <- mapM (\x -> getNewTypeVar) binds
    sts <- mapM (\(x,y) -> exprToSub' env x y) $ zip tys exs
    let tyshs = map (typeToTypeScheme env . snd) sts
    let env1 = filter (\(v,_) -> not (v `elem` names)) env ++ zip names tyshs
    let sub1 = zip tys (map snd sts) ++ foldr (++) [] (map fst sts)
    sub2 <- unifySub sub1
    (sub3, ty3) <- exprToSub' env1 ty body
    sub4 <- unifySub $ sub2 ++ sub3
    return (sub4, applySub sub4 ty)
      where f (([EE.Var s],_)) = EE.Var s
            f _ = EE.Var []
exprToSub' env ty (EE.MatchAllExpr dt mt (pt,ex)) = do
    tvdt <- getNewTypeVar
    tvex <- getNewTypeVar
    (sub1, ty1) <- exprToSub' env tvdt dt
    (sub2, ty2) <- exprToSub' env (TypeMatcher tvdt) mt
    (sub3, env1, ty3) <- patternToSub env (TypePattern tvdt) pt
    (sub4, ty4) <- exprToSub' env1 tvex ex
    sub5 <- unifySub $ (ty1, tvdt) : (ty2,TypeMatcher tvdt) : (ty3,TypePattern tvdt) : (ty4, tvex) : (ty,TypeCollection tvex) : sub1 ++ sub2 ++ sub3 ++ sub4
    return (sub5, applySub sub5 ty)
exprToSub' env ty _ = return ([], TypeStar)

