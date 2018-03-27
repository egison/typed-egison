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

import qualified Language.Egison.Expressions as EE
import Language.Egison.Expressions (Type(..), EgisonExpr(..), EgisonTopExpr(..), Env, refEnvImplConv, deleteEnvType)
import Language.Egison.Types (innersToExprs)
import Control.Monad.Reader (Reader, ask, local, runReader)

implConvTopExpr :: Env -> EgisonTopExpr -> [EgisonExpr]
implConvTopExpr env exp = case exp of
  Test e -> applyImplConv env e
  _ -> []

applyImplConv :: Env -> EgisonExpr -> [EgisonExpr]
applyImplConv env exp = runReader (applyImplConv' exp) env

applyImplConv' :: EgisonExpr -> Reader Env [EgisonExpr]
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
  return $ TupleExpr <$> ess
applyImplConv' (CollectionExpr es) = do
  let es1 = innersToExprs es
  ess <- mapM applyImplConv' es1
  return $ TupleExpr <$> (cartesian ess)
applyImplConv' (LambdaExpr args body) = do
    let args1 = filter (/= EE.Var []) $ map f args
    -- To realize shadowing of variables in args, we must delete args from environment
    body1 <- local (\e -> deleteEnvType e args1) $ applyImplConv' body
    return $ map (\x -> LambdaExpr args x) body1
      where f (EE.TensorArg s) = EE.Var [s]
            f _ = EE.Var []
applyImplConv' (ApplyExpr f e) = do
  f1 <- applyImplConv' f
  e1 <- applyImplConv' e
  return $ ApplyExpr <$> f1 <*> e1


-- This helper function take a list of list and return all Cartesian product.
-- For example, lltol [[1,2],[3,4]] ===>> [[1,3],[1,4],[2,3],[2,4]]
cartesian :: [[a]] -> [[a]]
cartesian [] = [[]]
cartesian (l:rest) = do
  a <- l
  as <- cartesian rest
  return (a:as)


applyImplConv'' :: EgisonExpr -> Type -> Reader Env [EgisonExpr]
applyImplConv'' e t = do
  env <- ask
  let ics = refEnvImplConv env t
  return $ e : map (\(t,f) -> (ApplyExpr f e)) ics
