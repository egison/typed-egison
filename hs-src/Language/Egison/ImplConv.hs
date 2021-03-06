{- |
Module      : Language.Egison.Types
Copyright   : Akira KAWATA
Licence     : MIT

This module contains implicit conversion algorithm for Egison
I suggest you to import this file using qualified import.
-}

module Language.Egison.ImplConv(
  implConvTopExpr
  , applyImplConv
  )where

import           Control.Monad.Reader        (Reader, ask, local, runReader)
import           Language.Egison.Expressions (Env, Expr (..), TopExpr (..),
                                              Type (..), deleteEnvType,
                                              refEnvAbsImplConv, refEnvImplConv)
import qualified Language.Egison.Expressions as EE

innersToExprs :: [EE.InnerExpr] -> [EE.Expr]
innersToExprs [] = []
innersToExprs (EE.ElementExpr e:rest) = e : innersToExprs rest
innersToExprs ((EE.SubCollectionExpr (EE.CollectionExpr is)):rest) =
    innersToExprs is ++ innersToExprs rest


implConvTopExpr :: Env -> TopExpr -> [Expr]
implConvTopExpr env exp = case exp of
  Test e -> applyImplConv env e
  _      -> []

applyImplConv :: Env -> Expr -> [Expr]
applyImplConv env exp = runReader (applyImplConv' exp) env

applyImplConv' :: Expr -> Reader Env [Expr]
applyImplConv' e@(CharExpr _) = applyImplConv'' e TypeChar
applyImplConv' e@(StringExpr _) = applyImplConv'' e TypeString
applyImplConv' e@(BoolExpr _) = applyImplConv'' e TypeBool
applyImplConv' e@(IntegerExpr _) = applyImplConv'' e TypeInt
-- I must modify here after implement type environment.
applyImplConv' e@(VarExpr _) = return [e]
applyImplConv' (IfExpr e1 e2 e3) = do
  e1s <- applyImplConv' e1
  e2s <- applyImplConv' e2
  e3s <- applyImplConv' e3
  return $ IfExpr <$> e1s <*> e2s <*> e3s
applyImplConv' (TupleExpr es) = do
  ess <- mapM applyImplConv' es
  return $ TupleExpr <$> cartesian ess
applyImplConv' (CollectionExpr es) = do
  let es1 = innersToExprs es
  ess <- mapM applyImplConv' es1
  return $ TupleExpr <$> (cartesian ess)
applyImplConv' (LambdaExpr args body) = do
    let args1 = filter (/= EE.Var []) $ map f args
    -- To realize shadowing of variables in args, we must delete args from environment
    body1 <- local (\e -> deleteEnvType args1 e) $ applyImplConv' body
    return $ map (\x -> LambdaExpr args x) body1
      where f (EE.TensorArg s) = EE.Var [s]
            f _                = EE.Var []
applyImplConv' (ApplyExpr f e) = do
  f1 <- applyImplConv' f
  e1 <- applyImplConv' e
  return $ ApplyExpr <$> f1 <*> e1
applyImplConv' (LetExpr binds exp) = do
  -- head is appended because the bug of let binds
  let vars = map (head.fst) binds
  let bodies = map snd binds
  bodies1 <- mapM applyImplConv' bodies
  exp1 <- local (\e -> deleteEnvType vars e) $ applyImplConv' exp
  return $ do
    let bodies2 = cartesian bodies1
    bodies3 <- bodies2
    exp2 <- exp1
    return $ LetExpr (zip (map fst binds) bodies3) exp2
applyImplConv' (LetRecExpr binds exp) = do
  es <- applyImplConv' (LetExpr binds exp)
  return $ map (\(LetExpr b e) -> LetRecExpr b e) es
applyImplConv' (MatchAllExpr e1 e2 (pt,e3)) = do
  e11 <- applyImplConv' e1
  e21 <- applyImplConv' e2
  e31 <- applyImplConv' e3
  return $ MatchAllExpr <$> e11 <*>  e21 <*> (zip (inf pt) e31)
    where
      inf x = x : inf x
applyImplConv' e@_ = return [e]

-- This helper function take a list of list and return all Cartesian product.
-- For example, cartesian [[1,2],[3,4]] ===>> [[1,3],[1,4],[2,3],[2,4]]
cartesian :: [[a]] -> [[a]]
cartesian [] = [[]]
cartesian (l:rest) = do
  a <- l
  as <- cartesian rest
  return (a:as)


applyImplConv'' :: Expr -> Type -> Reader Env [Expr]
applyImplConv'' e t = do
  env <- ask
  let ics = refEnvImplConv env t
  let aics = refEnvAbsImplConv env t
  if aics /= []
    then return $ map (\(t,f) -> (ApplyExpr f e)) aics
    else return $ e : map (\(t,f) -> (ApplyExpr f e)) ics
