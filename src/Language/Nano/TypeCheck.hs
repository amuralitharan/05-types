{-# LANGUAGE FlexibleInstances, OverloadedStrings, BangPatterns #-}
{-# LANGUAGE InstanceSigs #-}

module Language.Nano.TypeCheck where

import Language.Nano.Types
import Language.Nano.Parser

import qualified Data.List as L
import           Text.Printf (printf)  
import           Control.Exception (throw)
import Foreign (free)

--------------------------------------------------------------------------------
typeOfFile :: FilePath -> IO Type
typeOfFile f = parseFile f >>= typeOfExpr

typeOfString :: String -> IO Type
typeOfString s = typeOfExpr (parseString s)

typeOfExpr :: Expr -> IO Type
typeOfExpr e = do
  let (!st, t) = infer initInferState preludeTypes e
  if (length (stSub st)) < 0 then throw (Error ("count Negative: " ++ show (stCnt st)))
  else return t

--------------------------------------------------------------------------------
-- Problem 1: Warm-up
--------------------------------------------------------------------------------

-- | Things that have free type variables
class HasTVars a where
  freeTVars :: a -> [TId]

-- | Type variables of a type
instance HasTVars Type where
  freeTVars :: Type -> [TId]
  freeTVars TInt = []
  freeTVars TBool = []
  freeTVars (TVar a) = [a]
  freeTVars (TList l) = freeTVars l
  freeTVars (e1 :=> e2) = freeTVars e1 `L.union` freeTVars e2

-- | Free type variables of a poly-type (remove forall-bound vars)
instance HasTVars Poly where
  freeTVars :: Poly -> [TId]
  freeTVars (Mono t) = freeTVars t
  freeTVars (Forall v e) = L.delete v (freeTVars e)

-- | Free type variables of a type environment
instance HasTVars TypeEnv where
  freeTVars :: TypeEnv -> [TId]
  freeTVars gamma   = concat [freeTVars s | (x, s) <- gamma]  
  
-- | Look up a variable in a type environment
lookupVarType :: Id -> TypeEnv -> Poly
lookupVarType x ((y, s) : gamma)
  | x == y    = s
  | otherwise = lookupVarType x gamma
lookupVarType x [] = throw (Error ("unbound variable: " ++ x))

-- | Extend a type environment with a new binding
extendTypeEnv :: Id -> Poly -> TypeEnv -> TypeEnv
extendTypeEnv x s gamma = (x,s) : gamma  

-- | Look up a type variable in a substitution;
--   if not present, return the variable unchanged
lookupTVar :: TId -> Subst -> Type
lookupTVar v subst = maybe (TVar v) id (L.lookup v subst)

-- | Remove a type variable from a substitution
removeTVar :: TId -> Subst -> Subst
removeTVar v = L.deleteBy (\(x, _) (y, _) -> x == y) (v, undefined)

-- | Things to which type substitutions can be applied
class Substitutable a where
  apply :: Subst -> a -> a
  
-- | Apply substitution to type
instance Substitutable Type where  
  apply :: Subst -> Type -> Type
  apply _ TInt = TInt
  apply _ TBool = TBool
  apply sub (TVar v) = lookupTVar v sub
  apply sub (TList t) = TList (apply sub t)
  apply sub (e1 :=> e2) = apply sub e1 :=> apply sub e2

-- | Apply substitution to poly-type
instance Substitutable Poly where    
  apply :: Subst -> Poly -> Poly
  apply sub (Mono t) = Mono (apply sub t)
  apply sub (Forall vars t) = Forall vars (apply sub' t)
    where
      sub' = foldr removeTVar sub [vars]

-- | Apply substitution to (all poly-types in) another substitution
instance Substitutable Subst where  
  apply :: Subst -> Subst -> Subst
  apply sub to = zip keys (map (apply sub) vals)
    where
      (keys, vals) = unzip to
      
-- | Apply substitution to a type environment
instance Substitutable TypeEnv where  
  apply :: Subst -> TypeEnv -> TypeEnv
  apply sub gamma = zip keys (map (apply sub) vals)
    where
      (keys, vals) = unzip gamma
      
-- | Extend substitution with a new type assignment
extendSubst :: Subst -> TId -> Type -> Subst
extendSubst sub a t = (a, t') : sub'
  where
    t' = apply sub t
    sub' = map (\(x, y) -> (x, apply [(a, t')] y)) sub
--------------------------------------------------------------------------------
-- Problem 2: Unification
--------------------------------------------------------------------------------
      
-- | State of the type inference algorithm      
data InferState = InferState { 
    stSub :: Subst -- ^ current substitution
  , stCnt :: Int   -- ^ number of fresh type variables generated so far
} deriving (Eq,Show)

-- | Initial state: empty substitution; 0 type variables
initInferState = InferState [] 0

-- | Fresh type variable number n
freshTV n = TVar ("a" ++ show n)
    
-- | Extend the current substitution of a state with a new type assignment   
extendState :: InferState -> TId -> Type -> InferState
extendState (InferState sub n) a t = InferState (extendSubst sub a t) n
        
-- | Unify a type variable with a type; 
--   if successful return an updated state, otherwise throw an error
unifyTVar :: InferState -> TId -> Type -> InferState
unifyTVar st a t
  | TVar a == t = st
  | a `elem` freeTVars t = throw (Error ("type error: cannot unify " ++ a ++ " and " ++ show t ++ " (occurs check)"))
  | otherwise = extendState st a t
    
-- | Unify two types;
--   if successful return an updated state, otherwise throw an error
unify :: InferState -> Type -> Type -> InferState
unify st TInt TInt = st
unify st TBool TBool = st
unify st (TVar v) t = unifyTVar st v t
unify st t (TVar v) = unifyTVar st v t
unify st (t1 :=> t2) (t1' :=> t2') = st''
  where
    st' = unify st t1 t1'
    st'' = unify st' (apply (stSub st') t2) (apply (stSub st') t2')
unify st (TList t1) (TList t2) = unify st t1 t2
unify _ t1 t2 = throw (Error ("type error: cannot unify " ++ show t1 ++ " and " ++ show t2))

--------------------------------------------------------------------------------
-- Problem 3: Type Inference
--------------------------------------------------------------------------------    
  
infer :: InferState -> TypeEnv -> Expr -> (InferState, Type)
infer st _ (EInt _) = (st, TInt)
infer st _ (EBool _) = (st, TBool)
infer st _ ENil =
  let tv = freshTV (stCnt st)
  in (st { stCnt = stCnt st + 1 }, TList tv)
infer st gamma (EVar x) =
  let poly = lookupVarType x gamma
      (n, t) = instantiate (stCnt st) poly
  in (st { stCnt = n }, t)
infer st gamma (ELam x body) =
  let tv = freshTV (stCnt st)
      st' = st { stCnt = stCnt st + 1 }
      gamma' = extendTypeEnv x (Mono tv) gamma
      (st'', tBody) = infer st' gamma' body
      tLam = apply (stSub st'') (tv :=> tBody)
  in (st'', tLam)
infer st gamma (EApp e1 e2) =
  let (st1, t1) = infer st gamma e1
      (st2, t2) = infer st1 gamma e2
      tv = freshTV (stCnt st2)
      st3 = st2 { stCnt = stCnt st2 + 1 }
      st4 = unify st3 t1 (t2 :=> tv)
  in (st4, apply (stSub st4) tv)
infer st gamma (ELet x e1 e2) =
  let tv = freshTV (stCnt st)
      st' = st { stCnt = stCnt st + 1 }
      gamma' = extendTypeEnv x (Mono tv) gamma
      (st1, t1) = infer st' gamma' e1
      st2 = unify st1 tv t1 -- Unify the assumed type with the inferred type
      t1' = apply (stSub st2) t1
      poly = generalize (apply (stSub st2) gamma) t1'
      gamma'' = extendTypeEnv x poly gamma
      (st3, t2) = infer st2 gamma'' e2
  in (st3, t2)
infer st gamma (EBin op e1 e2) =
  let (st1, t1) = infer st gamma e1
      (st2, t2) = infer st1 gamma e2
      (st3, ty) = case op of
                    Plus  -> let st3 = unify st2 t1 TInt
                                 st4 = unify st3 t2 TInt
                             in (st4, TInt)
                    Minus -> let st3 = unify st2 t1 TInt
                                 st4 = unify st3 t2 TInt
                             in (st4, TInt)
                    Mul   -> let st3 = unify st2 t1 TInt
                                 st4 = unify st3 t2 TInt
                             in (st4, TInt)
                    Div   -> let st3 = unify st2 t1 TInt
                                 st4 = unify st3 t2 TInt
                             in (st4, TInt)
                    Eq    -> let st3 = unify st2 t1 t2
                             in (st3, TBool)
                    Ne    -> let st3 = unify st2 t1 t2
                             in (st3, TBool)
                    Lt    -> let st3 = unify st2 t1 TInt
                                 st4 = unify st3 t2 TInt
                             in (st4, TBool)
                    Le    -> let st3 = unify st2 t1 TInt
                                 st4 = unify st3 t2 TInt
                             in (st4, TBool)
                    And   -> let st3 = unify st2 t1 TBool
                                 st4 = unify st3 t2 TBool
                             in (st4, TBool)
                    Or    -> let st3 = unify st2 t1 TBool
                                 st4 = unify st3 t2 TBool
                             in (st4, TBool)
                    Cons  -> let tv = freshTV (stCnt st2)
                                 st3 = unify st2 t2 (TList tv)
                                 st4 = unify st3 t1 tv
                             in (st4, TList tv)
  in (st3, ty)
infer st gamma (EIf e1 e2 e3) =
  let (st1, t1) = infer st gamma e1
      (st2, t2) = infer st1 gamma e2
      (st3, t3) = infer st2 gamma e3
      st4 = unify st3 t1 TBool
      st5 = unify st4 t2 t3
  in (st5, apply (stSub st5) t2)

-- | Generalize type variables inside a type
generalize :: TypeEnv -> Type -> Poly
generalize gamma t =
  let envTVars = freeTVars gamma
      typeTVars = freeTVars t
      newTVars = typeTVars L.\\ envTVars
  in foldr Forall (Mono t) newTVars
    
-- | Instantiate a polymorphic type into a mono-type with fresh type variables
instantiate :: Int -> Poly -> (Int, Type)
instantiate n s = helper n [] s
  where
    helper :: Int -> Subst -> Poly -> (Int, Type)
    helper n sub (Mono t)     = (n, apply sub t)
    helper n sub (Forall a s) = helper (n + 1) ((a, freshTV n):sub) s
      
-- | Types of built-in operators and functions      
preludeTypes :: TypeEnv
preludeTypes =
  [ ("+",    Mono (TInt :=> TInt :=> TInt))
  , ("-",    Mono (TInt :=> TInt :=> TInt))
  , ("*",    Mono (TInt :=> TInt :=> TInt))
  , ("/",    Mono (TInt :=> TInt :=> TInt))
  , ("==",   Mono (TInt :=> TInt :=> TBool))
  , ("!=",   Mono (TInt :=> TInt :=> TBool))
  , ("<",    Mono (TInt :=> TInt :=> TBool))
  , ("<=",   Mono (TInt :=> TInt :=> TBool))
  , ("&&",   Mono (TBool :=> TBool :=> TBool))
  , ("||",   Mono (TBool :=> TBool :=> TBool))
  , ("if",   Forall "a" (Mono (TBool :=> TVar "a" :=> TVar "a" :=> TVar "a")))
  , ("[]",   Forall "a" (Mono (TList (TVar "a"))))
  , (":",    Forall "a" (Mono (TVar "a" :=> TList (TVar "a") :=> TList (TVar "a"))))
  , ("head", Forall "a" (Mono (TList (TVar "a") :=> TVar "a")))
  , ("tail", Forall "a" (Mono (TList (TVar "a") :=> TList (TVar "a"))))
  ]
