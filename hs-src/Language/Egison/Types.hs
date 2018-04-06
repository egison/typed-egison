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
import Debug.Trace
import Data.Char (ord,chr)

-- First element of Restriction will be type valiable.
-- Second element of Restriction is what the first element refer.
data TypeScheme = TypeScheme [TypeVarIndex] Type deriving Show
type Restriction = (Type,Type)
type Substitution = [Restriction]
-- [(Variable name, Type)]
type TypeSchemeEnvironment = [(EE.Var,TypeScheme)]
type MakeSubstitionM = ExceptT String (State TypeVarIndex)

unusedSuffix = "#"
finalExprTypeVar = "##"

checkTopExpr :: EE.Env -> EE.TopExpr -> Either String Type
checkTopExpr env (EE.Test e) = do
  (s,_) <- exprToSub env e
  let r = findAns s
  return r
    where findAns [] = TypeStar
          findAns ((t1,t2):r)
            | t1 == TypeVar finalExprTypeVar = t2
            | t2 == TypeVar finalExprTypeVar = t1
            | otherwise = findAns r
checkTopExpr env (EE.Define (EE.VarWithIndexType vn _) exp) = do
  ty <- checkTopExpr env (EE.Test (EE.LetRecExpr [([EE.Var [vn]],exp)] exp))
  case EE.refEnvType (EE.Var [vn]) env of
    Nothing -> return ty
    Just ty' -> if check then return ty else Left $ "Declared type " ++ show ty' ++ " and infered type " ++ show ty ++ " don't match."
      where
        check = case evalState (runExceptT (unifySub [(ty,ty')])) "###" of
          Right _ -> True
          Left _ -> False
checkTopExpr env _ = Right TypeStar

typeVarIndexCache :: IORef TypeVarIndex
typeVarIndexCache = unsafePerformIO $ newIORef "b"

nextString :: String -> String
nextString s = itos (stoi s + 1)
  where
    stoi "" = 0
    stoi (a:rest) = (ord a - ord 'a') + stoi rest * 26
    itos i = if i < 26 then [chr (i + ord 'a')] else chr (i`mod`26 + ord 'a') : itos (i`div`26)

exprToSub :: EE.Env -> EE.Expr -> Either String (Substitution, Type)
exprToSub env exp = unsafePerformIO $ exprToSubIO env exp

exprToSubIO :: EE.Env -> EE.Expr -> IO (Either String (Substitution, Type))
exprToSubIO env exp = do
  i <- readIORef typeVarIndexCache
  let (a,s) = runState (runExceptT $ exprToSub' env1 (TypeVar finalExprTypeVar) exp) i
  writeIORef typeVarIndexCache (nextString s)
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
applySub s (TypeMatcherClause t) = TypeMatcherClause (applySub s t)
applySub _ t = t

freeTypeVarIndex :: Type -> [TypeVarIndex]
freeTypeVarIndex = nub . freeTypeVarIndex'
    where
        freeTypeVarIndex' (TypeVar i) = if 'a' <= head i && head i <= 'z' then [i] else []
        freeTypeVarIndex' (TypeFun t1 t2) = freeTypeVarIndex' t1 ++ freeTypeVarIndex' t2
        freeTypeVarIndex' (TypeTuple ts) = concatMap freeTypeVarIndex' ts
        freeTypeVarIndex' (TypeCollection t1) = freeTypeVarIndex' t1
        freeTypeVarIndex' (TypePattern t1) = freeTypeVarIndex' t1
        freeTypeVarIndex' (TypeMatcher t1) = freeTypeVarIndex' t1
        freeTypeVarIndex' (TypeMatcherClause t1) = freeTypeVarIndex' t1
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
    TypeMatcherClause t -> TypeMatcherClause (replace t1 t2 t)
    _ -> t3

-- replace all t1 in s with t2
replaceSubstituition :: Type -> Type -> Substitution -> Substitution
replaceSubstituition t1 t2 s = map (\(x,y) -> ((replace t1 t2 x), (replace t1 t2 y))) s

isADT :: Type -> Bool
isADT (TypeVar s) = ord 'A' <= ord (head s) && ord (head s) <= ord 'Z'

isRealTypeVar :: Type -> Bool
isRealTypeVar t@(TypeVar s) = not $ isADT t
isRealTypeVar _ = False

unifySub :: Substitution -> MakeSubstitionM Substitution
unifySub [] = return []
unifySub ((t1, t2) : r)
    | t1 == t2 = unifySub r
    | otherwise = case (t1, t2) of
        ((TypeFun t3 t4),(TypeFun t5 t6)) -> unifySub ((t3,t5):(t4,t6):r)
        (TypeTuple ts1, TypeTuple ts2) -> if length ts1 == length ts2
          then unifySub $ (zip ts1 ts2) ++ r
          else throwError "Lengths of tuple are not equal."
        (TypeCollection t3,TypeCollection t4) -> unifySub $ (t3,t4):r
        (TypePattern t3,TypePattern t4) -> unifySub $ (t3,t4):r
        (TypeMatcher t3,TypeMatcher t4) -> unifySub $ (t3,t4):r
        (TypeMatcherClause t3, TypeMatcherClause t4) -> unifySub $ (t3,t4):r
        (TypeFun (TypeTuple []) t3,t4) -> unifySub $ (t3,t4):r
        (t3,TypeFun (TypeTuple []) t4) -> unifySub $ (t3,t4):r
        (TypeVar tv1,t4) -> if tv1 `elem` freeTypeVarIndex t4
            then throwError "Type variable is occured recursively."
            else if isADT (TypeVar tv1)
                  then if isRealTypeVar t4
                    then unifySub $ (t4, TypeVar tv1) : r
                    else throwError $ "Try to unify " ++ show t1 ++ " and " ++ show t2
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
  put (nextString i)
  return $ TypeVar $ i ++ unusedSuffix

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
patternToSub :: TypeSchemeEnvironment -> Type -> EE.EgisonPattern -> MakeSubstitionM (Substitution, Type, TypeSchemeEnvironment)
patternToSub env (TypePattern ty) (EE.ValuePat exp) = do
  (sub1, ty1) <- exprToSub' env ty exp
  sub2 <- unifySub $ (ty,ty1) : sub1
  return (sub2, applySub sub2 (TypePattern ty1), env)
patternToSub env (TypePattern ty) (EE.PatVar var) = do
  tv <- getNewTypeVar
  let env1 = (var,TypeScheme [] tv) : env
  let sub = [(ty, tv)]
  return (sub, applySub sub (TypePattern ty), env1)
patternToSub env (TypePattern ty) (EE.InductivePat pc pats) = do
  pctype <- lookupTypeSchemeEnv (EE.Var [pc]) env >>= instantiateTypeScheme
  (sub1, env1, tys1) <- f env pats
  sub2 <- unifySub $ (pctype, TypeFun (TypeTuple tys1) (TypePattern ty)) : sub1
  return (sub2, applySub sub2 (TypePattern ty), env1)
  where
    f :: TypeSchemeEnvironment -> [EE.EgisonPattern] -> MakeSubstitionM (Substitution, TypeSchemeEnvironment, [Type])
    f env [] = return ([], env, [])
    f env (p:rest) = do
      ty1 <- getNewTypeVar
      (sub2,ty2,env2) <- patternToSub env (TypePattern ty1) p
      (sub3,env3,tys3) <- f env2 rest
      return ((TypePattern ty1,ty2) : sub3, env3, ty2:tys3)
patternToSub env (TypePattern _) EE.WildCard = return ([], TypeStar, env)
patternToSub env (TypePattern _) _ = return ([], TypeStar, env)
patternToSub _ ty _ = throwError $ "Pattern is typed as non-pattern type " ++ show ty


exprToSub' :: TypeSchemeEnvironment -> Type -> EE.Expr -> MakeSubstitionM (Substitution, Type)
exprToSub' env ty (EE.CharExpr _ ) = return ([(ty,TypeChar)], TypeChar)
exprToSub' env ty (EE.StringExpr _) = return ([(ty,TypeString)], TypeString)
exprToSub' env ty (EE.BoolExpr _) = return ([(ty,TypeBool)], TypeBool)
exprToSub' env ty (EE.IntegerExpr _) = return ([(ty,TypeInt)], TypeInt)
exprToSub' env ty (EE.VarExpr vn) = do
    ty' <- lookupTypeSchemeEnv vn env >>= instantiateTypeScheme
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
    let ce p = catchE p (\x -> throwError $ x ++ "\nThe elements of collection do not have the same type.\n" ++ show es ++ "\n" ++ show ((ty, TypeCollection ty2) : (ty, TypeCollection ty1) : sub1 ++ sub2))
    sub3 <- ce $ unifySub $ ((ty, TypeCollection ty2) : (ty, TypeCollection ty1) : sub1 ++ sub2)
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
exprToSub' env ty (EE.InductiveDataExpr cnstr args) = do
    tycnstr <- lookupTypeSchemeEnv (EE.Var [cnstr]) env >>= instantiateTypeScheme
    tvargs <- mapM (\x -> getNewTypeVar) args
    sts1 <- mapM (\(e,t) -> exprToSub' env t e) (zip args tvargs)
    let sub1 = concat $ map fst sts1
    let tys1 = map snd sts1
    let ce p = catchE p (\x -> throwError $ x ++ "Wrong arguments are passed to data constructor" ++ cnstr)
    sub2 <- ce $ unifySub $ (tycnstr, TypeFun (TypeTuple tvargs) ty) : sub1
    return (sub2, applySub sub2 ty)
exprToSub' env ty (EE.LetExpr binds body) = do
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
    (sub3, ty3, env1) <- patternToSub env (TypePattern tvdt) pt
    (sub4, ty4) <- exprToSub' env1 tvex ex
    sub5 <- unifySub $ (ty1, tvdt) : (ty2,TypeMatcher tvdt) : (ty3,TypePattern tvdt) : (ty4, tvex) : (ty,TypeCollection tvex) : sub1 ++ sub2 ++ sub3 ++ sub4
    return (sub5, applySub sub5 ty)
exprToSub' env ty (EE.MatchExpr dt mt mcs) = do
    tvdt <- getNewTypeVar
    tvex <- getNewTypeVar
    (sub1, ty1) <- exprToSub' env tvdt dt
    (sub2, ty2) <- exprToSub' env (TypeMatcher tvdt) mt
    subs3 <- mapM (mctosub env tvdt tvex) mcs
    sub4 <- unifySub $ (ty, tvex) : (concat $ sub1 : sub2 : subs3)
    return (sub4, applySub sub4 ty)
      where
        mctosub env tvdt tvex (pt, ex) = do
          (s1, _, e1) <- patternToSub env (TypePattern tvdt) pt
          (s2, _) <- exprToSub' e1 tvex ex
          let ce p = catchE p (\x -> throwError $ x ++ "\nUnification error in exprToSub'(mctosub) EE.MatchExpr.")
          s3 <- unifySub $ s1 ++ s2
          return s3
exprToSub' env ty (EE.MatcherBFSExpr es) = do
  ty1 <- getNewTypeVar
  sts <- mapM (mcsToSub env (TypeMatcherClause ty1)) es
  let sub1 = foldr (++) [] (map fst sts)
  let sub2 = map (\x -> (TypeMatcherClause ty1, snd x)) sts
  let ce p = catchE p (\x -> throwError $ x ++ "\nUnification error in exprToSub' EE.MatcherBFSExpr")
  sub3 <- ce $ unifySub $ ((ty, TypeMatcher ty1) : sub1 ++ sub2)
  return (sub3, applySub sub3 ty)
exprToSub' env ty (EE.MatcherDFSExpr es) = do
  ty1 <- getNewTypeVar
  sts <- mapM (mcsToSub env (TypeMatcherClause ty1)) es
  let sub1 = foldr (++) [] (map fst sts)
  let sub2 = map (\x -> (TypeMatcherClause ty1, snd x)) sts
  let ce p = catchE p (\x -> throwError $ x ++ "\nUnification error in exprToSub' EE.MatcherBFSExpr")
  sub3 <- ce $ unifySub $ ((ty, TypeMatcher ty1) : sub1 ++ sub2)
  return (sub3, applySub sub3 ty)
exprToSub' env ty EE.SomethingExpr = do
  tv1 <- getNewTypeVar
  sub1 <- unifySub $ [(ty, TypeMatcher tv1)]
  return (sub1, applySub sub1 ty)
exprToSub' env ty _ = return ([], TypeStar)


-- This function return TypeMatcherClause
mcsToSub :: TypeSchemeEnvironment -> Type -> (EE.PrimitivePatPattern, EE.Expr, [(EE.PrimitiveDataPattern, EE.Expr)]) -> MakeSubstitionM (Substitution, Type)
mcsToSub env ty (ppp,nme,pdmcs) = do
  ty1 <- getNewTypeVar
  (sub2, _, env2, holes) <- pppToSub env (TypePattern ty1) ppp
  (sub3, _) <- exprToSub' env (tupleToMathcerTuple holes) nme
  typdp <- getNewTypeVar
  sts <- mapM (pdmcToSub (env ++ env2) (TypeTuple [typdp,TypeCollection holes])) pdmcs
  let sub4 = foldr (++) [] (map fst sts)
  let sub5 = map (\x -> (TypeTuple [typdp,TypeCollection holes], snd x)) sts
  let ce p = catchE p (\x -> throwError $ x ++ "\nUnification error in mcsToSub")
  sub6 <- ce (unifySub $ (ty, TypeMatcherClause ty1) : sub2 ++ sub3 ++ sub4 ++ sub5)
  return (sub6, applySub sub6 $ TypeMatcherClause ty1)


-- The third value in the return value is a free variables in the given pattern
-- The forth value in the return value is a tuple which contain all "$" in the given pattern
pppToSub :: TypeSchemeEnvironment -> Type -> EE.PrimitivePatPattern -> MakeSubstitionM (Substitution, Type, TypeSchemeEnvironment, Type)
pppToSub env ty EE.PPWildCard = return ([], TypeStar, env, TypeTuple [])
pppToSub env ty EE.PPPatVar = do
  ty1 <- getNewTypeVar
  let cc = (\x -> throwError "Unification error in pppToSub EE.PPPatVar")
  sub1 <- catchE (unifySub [(ty,TypePattern ty1)]) cc
  return (sub1, applySub sub1 ty, env, TypeTuple [ty1])
pppToSub env ty (EE.PPValuePat s) = do
  ty1 <- getNewTypeVar
  let cc = (\x -> throwError "Unification error in pppToSub EE.PPValuePat")
  sub1 <- catchE (unifySub [(ty,TypePattern ty1)]) cc
  return (sub1, applySub sub1 ty, (EE.Var [s],TypeScheme [] ty1):env, TypeTuple [])
pppToSub env ty (EE.PPInductivePat fname []) = do
  ftype <- lookupTypeSchemeEnv (EE.Var [fname]) env >>= instantiateTypeScheme
  sub1 <- unifySub [(ftype, ty)]
  return (sub1, applySub sub1 ftype, env, TypeTuple [])
pppToSub env ty (EE.PPInductivePat fname ppps) = do
  ftype <- lookupTypeSchemeEnv (EE.Var [fname]) env >>= instantiateTypeScheme
  (sub1, env1, tys1, ty1) <- f env ppps
  let ce p = catchE p (\x -> throwError $ x ++ "\nUnification error in pppToSub EE.PPInductivePat")
  sub2 <- ce $ unifySub $ (ftype, TypeFun (TypeTuple tys1) ty) : sub1
  return (sub2, applySub sub2 ty, env1, ty1)
   where
    -- The third value in the return value arguments for the function
    -- The forth value in the return value is a tuple which contain all "$" in the given pattern
    f :: TypeSchemeEnvironment -> [EE.PrimitivePatPattern] -> MakeSubstitionM (Substitution, TypeSchemeEnvironment, [Type], Type)
    f env [] = return ([], env, [], TypeTuple [])
    f env (p:rest) = do
      ty1 <- getNewTypeVar
      (sub2,ty2,env2,TypeTuple args2) <- pppToSub env ty1 p
      (sub3,env3,tys3,TypeTuple args3) <- f (env ++ env2) rest
      return ((ty1,ty2) : (sub2 ++ sub3), env3, ty2:tys3, TypeTuple $ args2 ++ args3)


-- The second return value is just a type not a TypePattern _.
-- The third value in the return value is
-- a environment appended free variables in the given pattern
pdpToSub :: TypeSchemeEnvironment -> Type -> EE.PrimitiveDataPattern -> MakeSubstitionM (Substitution, Type, TypeSchemeEnvironment)
pdpToSub env ty EE.PDWildCard = return ([], TypeStar, env)
pdpToSub env ty (EE.PDPatVar s) = do
  ty1 <- getNewTypeVar
  let env1 = (EE.Var [s], TypeScheme [] ty1) : env
  return ([(ty1, ty)], ty1, env1)
pdpToSub env ty (EE.PDInductivePat fname []) = do
  ftype <- lookupTypeSchemeEnv (EE.Var [fname]) env >>= instantiateTypeScheme
  let ce p = catchE p (\x -> throwError $ x ++ "\nUnification error in pdpToSub EE.PDInductivePat")
  sub1 <- ce $ unifySub $ [(ftype, ty)]
  return (sub1, applySub sub1 ftype, env)
pdpToSub env ty (EE.PDInductivePat fname pdps) = do
  ftype <- lookupTypeSchemeEnv (EE.Var [fname]) env >>= instantiateTypeScheme
  (sub1, env1, tys1) <- f env pdps
  let ce p = catchE p (\x -> throwError $ x ++ "\nUnification error in pdpToSub EE.PDInductivePat")
  sub2 <- ce $ unifySub $ (ftype, TypeFun (TypeTuple tys1) ty) : sub1
  return (sub2, applySub sub2 ty, env1)
  where
    f :: TypeSchemeEnvironment -> [EE.PrimitiveDataPattern] -> MakeSubstitionM (Substitution, TypeSchemeEnvironment, [Type])
    f env [] = return ([], env, [])
    f env (p:rest) = do
      ty1 <- getNewTypeVar
      (sub2,ty2,env2) <- pdpToSub env ty1 p
      (sub3,env3,tys3) <- f env2 rest
      return ((ty1,ty2) : sub3, env3, ty2:tys3)
pdpToSub env ty exp = throwError $ "Not implemented ! " ++ show exp ++ "\n"


-- The return values is a tuple of substitution and
-- (TypeTuple [type of pdp, type of exp])
pdmcToSub :: TypeSchemeEnvironment -> Type -> (EE.PrimitiveDataPattern, EE.Expr) -> MakeSubstitionM (Substitution, Type)
pdmcToSub env (ty@(TypeTuple [typdp,TypeCollection holes])) (pdp, exp) = do
  (sub1, ty1, env1) <- pdpToSub env typdp pdp
  (sub2, ty2) <- exprToSub' env1 (TypeCollection holes) exp
  let ce p = catchE p (\x -> throwError $ x ++ "\nUnification error in pdmcToSub")
  sub3 <- ce $ unifySub $ sub1 ++ sub2
  return (sub3, applySub sub3 ty)


tupleToMathcerTuple :: Type -> Type
tupleToMathcerTuple (TypeTuple ts) = TypeTuple (map TypeMatcher ts)

