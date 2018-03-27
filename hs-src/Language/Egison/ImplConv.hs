{- |
Module      : Language.Egison.Types
Copyright   : Akira Kawata
Licence     : MIT

This module contains implicit conversion algorithm for Egison
I suggest you to import this file using qualified import.
-}

module Language.Egison.ImplConv(
  implConvTopExpr
  , applyImplConv
  )where

import qualified Language.Egison.Expressions as EE
import Language.Egison.Expressions (Type(..), TypeVarIndex, EgisonExpr(..), EgisonTopExpr(..), Env, refEnvImplConv)
import Control.Monad.Reader (Reader, ask, runReader)

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

applyImplConv'' :: EgisonExpr -> Type -> Reader Env [EgisonExpr]
applyImplConv'' e t = do
  env <- ask
  let ics = refEnvImplConv env t
  return $ e : map (\(t,f) -> (ApplyExpr f e)) ics
