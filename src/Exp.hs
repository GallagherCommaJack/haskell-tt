{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeOperators     #-}
module Exp where
import           Data.Map    (Map)
import qualified Data.Map    as M
import           Data.String

type (|->) = Map

-- uses a locally nameless approach
data Exp = Set Int | Exp :-> Exp
         | FVar String | BVar  Int
         | Lam  Exp Exp  | Exp :#: Exp
         deriving (Read, Eq)

infixr 2 :->
infixl 5 :#:

isAtomic :: Exp -> Bool
isAtomic (Set _) = True
isAtomic (BVar _) = True
isAtomic (FVar _) = True
isAtomic _ = False

instance Show Exp where
  show (Set i) = "Set " ++ show i
  show (a@(_ :-> _) :-> b) = "(" ++ show a ++ ") :-> " ++ show b
  show (a :-> b) = show a ++ " :-> " ++ show b
  show (FVar s) = s
  show (BVar n) = show n
  show (Lam a b) = "λ " ++ show a ++ ". " ++ show b
  show (f :#: x) | isAtomic x = show f ++ " " ++ show x
                 | otherwise  = show f ++ " (" ++ show x ++ ")"

instance IsString Exp where
  fromString = FVar

liftExp :: Int -> Int -> Exp -> Exp
liftExp d n (Lam a b) = Lam (liftExp d n a) (liftExp (d + 1) n b)
liftExp d n (f :#: x) = liftExp d n f :#: liftExp d n x
liftExp d n (BVar i) = BVar (if d <= i then n + i else i)
liftExp d n (a :-> b) = liftExp d n a :-> liftExp (d + 1) n b
liftExp _ _ e = e

wkExp :: Int -> Exp -> Exp
wkExp = liftExp 0

substExp :: Int -> Exp -> Exp -> Exp
substExp d v (Lam a b) = Lam (substExp d v a) (substExp (d + 1) v b)
substExp d v (f :#: x) = substExp d v f :#: substExp d v x
substExp d v (BVar i) = case compare d i of
                          LT -> BVar (i - 1)
                          EQ -> wkExp d v
                          GT -> BVar i
substExp d v (a :-> b) = substExp d v a :-> substExp (d + 1) v b
substExp _ _ e = e

substNames :: (String -> Maybe Exp) -> Exp -> Exp
substNames f = go 0
  where go n (FVar i) = maybe (FVar i) (wkExp n) $ f i
        go n (a :-> b) = go n a :-> go (n + 1) b
        go n (Lam a b) = Lam (go n a) (go (n + 1) b)
        go n (f :#: x) = go n f :#: go n x
        go _ e = e

substEnv :: (String |-> Exp) -> Exp -> Exp
substEnv m = substNames (flip M.lookup m)

substName :: String -> Exp -> Exp -> Exp
substName s e = substNames (\i -> if i == s then Just e else Nothing)
rename :: (String,String) -> Exp -> Exp
rename (s1,s2) = substName s1 (FVar s2)
