{-# LANGUAGE FlexibleContexts #-}
import Control.Monad.Error
import Control.Monad
import Data.List
import Data.Monoid
import System.Random
import System.IO.Unsafe
import Data.Char

infixl 2 :@
infixr 3 :->

type Symb = String

-- Терм
data Expr =
  Var Symb
  | Expr :@ Expr
  | Lam Symb Expr
     deriving (Eq,Show)

-- Тип
data Type =
  TVar Symb
  | Type :-> Type
    deriving (Eq,Show)

-- Контекст
newtype Env = Env [(Symb,Type)]
  deriving (Eq,Show)

-- Подстановка
newtype SubsTy = SubsTy [(Symb, Type)]
  deriving (Eq,Show)

freeVars :: Expr -> [Symb]
freeVars (Var a) = [a]
freeVars (a :@ b) = union (freeVars a) (freeVars b)
freeVars (Lam a expr) = filter (/= a) (freeVars expr)


freeTVars :: Type -> [Symb]
freeTVars (TVar a) = [a]
freeTVars (a :-> b) =  union (freeTVars a) (freeTVars b)

envDuplCheck :: Env -> Symb -> Bool
envDuplCheck (Env []) s = False
envDuplCheck (Env list) s = if((fst $ (head list)) == s) then True else envDuplCheck (Env (tail list)) s

extendEnv :: Env -> Symb -> Type -> Env
extendEnv (Env env) symb t = if(envDuplCheck (Env env) symb) then (Env env) else (Env((symb, t) : env))

freeTVarsEnv :: Env -> [Symb]
freeTVarsEnv (Env []) = []
freeTVarsEnv (Env e) = union (freeTVars (snd (head e))) (freeTVarsEnv (Env(tail e)))

appEnv :: (MonadError String m) => Env -> Symb -> m Type
appEnv (Env []) v = throwError ("There is no variable \"" ++ v ++ "\" in the enviroment.")
appEnv (Env e) v = if (fst (head e)) == v
					  then return (snd (head e))
					  else appEnv (Env (tail e)) v

appSubsTy :: SubsTy -> Type -> Type
appSubsTy (SubsTy []) t = t
appSubsTy (SubsTy list) (TVar symbol) = if(fst(head list)) == symbol
										then (snd (head list))
										else appSubsTy (SubsTy(tail list)) (TVar symbol)
appSubsTy subs (a:-> b) = ((appSubsTy subs a) :-> (appSubsTy subs b))

appSubsEnv :: SubsTy -> Env -> Env
appSubsEnv s (Env xs) = Env $ map (\x -> (fst x, appSubsTy s (snd x))) xs

composeToOne :: SubsTy -> (Symb, Type) -> (Symb, Type)
composeToOne (SubsTy []) sub = sub
composeToOne (SubsTy list) (s, TVar t) = if(fst $ head list) == t then (s, snd $ head list)
										 else composeToOne (SubsTy (tail list)) (s, TVar t)
composeToOne subs (s, a :-> b) = (s, (snd (composeToOne subs (s, a)) :-> snd (composeToOne subs (s,b))))

composeSubsTyAnswer :: SubsTy -> SubsTy -> [(Symb, Type)] -> [Symb] -> [(Symb, Type)]
composeSubsTyAnswer (SubsTy []) (SubsTy []) answer used = answer
composeSubsTyAnswer (SubsTy mainList) (SubsTy []) answer used = if(elem (fst(head mainList)) used)
							then composeSubsTyAnswer (SubsTy (tail mainList)) (SubsTy []) answer used
							else composeSubsTyAnswer (SubsTy (tail mainList)) (SubsTy []) (answer ++ [(head mainList)]) (used ++ [fst(head mainList)])
composeSubsTyAnswer mainSub (SubsTy list) answer used = composeSubsTyAnswer mainSub (SubsTy (tail list)) (answer ++ [(composeToOne mainSub (head list))]) (used ++ [(fst(head list))])

composeSubsTy :: SubsTy -> SubsTy -> SubsTy
composeSubsTy (SubsTy []) sub = sub
composeSubsTy sub (SubsTy []) = sub
composeSubsTy mainSub sub = SubsTy(composeSubsTyAnswer mainSub sub [] [])

instance Monoid SubsTy where
	mempty = SubsTy []
	mappend  = composeSubsTy

equalCheck :: Type -> Type -> Bool
equalCheck (TVar s1)(TVar s2) = (s1 == s2)
equalCheck (TVar s) t = False
equalCheck t (TVar s) = False
equalCheck (t1 :-> t2) (t3 :-> t4) = (equalCheck t1 t3) && (equalCheck t2 t4)

unifyCheck :: Type -> Type -> Bool
unifyCheck (TVar t1) (TVar t2) = (t1 /= t2)
unifyCheck (TVar s) (t1 :-> t2) = (unifyCheck (TVar s) t1) && (unifyCheck (TVar s) t2)
unifyCheck (t1 :-> t2) (TVar s) = (unifyCheck (TVar s) t1) && (unifyCheck (TVar s) t2)
unifyCheck (t1 :-> t2) (t3 :-> t4) = (unifyCheck t1 t3) && (unifyCheck t2 t4)

getSubs :: Type -> Type -> [(Symb, Type)]
getSubs (TVar s) t = [(s, t)]
getSubs t (TVar s) = [(s, t)]
getSubs (t1 :-> t2) (t3 :-> t4) = (getSubs t1 t3) ++ (getSubs t2 t4)

unify :: (MonadError String m) => Type -> Type -> m SubsTy
unify t1 t2   |(equalCheck t1 t2) = return $ SubsTy []
			  |(unifyCheck t1 t2) = return $ SubsTy (getSubs t1 t2)
			  | otherwise = throwError ("Can't unify (" ++ (show t1) ++ ") with (" ++ (show t2) ++ ")!")

randNumUnsafe :: (Random a, Num a) => [a]
randNumUnsafe = unsafePerformIO $ liftM (take 6 . randomRs (9, 15)) newStdGen

equations :: (MonadError String m) => Env -> Expr -> Type -> m [(Type,Type)]
equations env (Var s) t = do
         t1 <- appEnv env s
         return [(t1, t)]
equations env (m :@ n) t = do
    let newVar = TVar (map intToDigit randNumUnsafe )
    e1 <- equations env m (newVar :-> t)
    e2 <- equations env n newVar
    return $ e1 ++ e2
equations env (Lam x m) t = do
    let a = TVar (map intToDigit randNumUnsafe )
    let b = TVar (map intToDigit randNumUnsafe )
    e1 <- equations (extendEnv env x a) m b
    return $ e1 ++ [(a :-> b, t)]

solveOne :: (Type, Type) -> SubsTy
solveOne (a,b) = do
    let Right ans = unify a b
    ans

principlePair :: (MonadError String m) =>  Expr -> m (Env,Type)
principlePair exp = do
    let env = Env $ map (\x -> (x,TVar $ x ++ "'")) (freeVars exp)
    let t   = TVar (map intToDigit randNumUnsafe)
    eq <- equations env exp t

    let a = foldr (\x y -> ((fst x :-> fst y),(snd x :-> snd y))) (head eq) (tail eq)
    let s = unify (fst a) (snd a)

    case s of
        Left err -> throwError $ err
        Right s  -> return $ (appSubsEnv s env, appSubsTy s t)
