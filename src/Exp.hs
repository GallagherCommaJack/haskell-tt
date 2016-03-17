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

bvarsOp :: (Int -> Int -> Exp) -> Int -> Exp -> Exp
bvarsOp op d (BVar i) = op d i
bvarsOp op d (a :-> b) = bvarsOp op d a :-> bvarsOp op (d + 1) b
bvarsOp op d (Lam a b) = Lam (bvarsOp op d a) (bvarsOp op (d + 1) b)
bvarsOp op d (f :#: x) = bvarsOp op d f :#: bvarsOp op d x
bvarsOp _ _ e = e

fvarsOp :: (String -> Maybe Exp) -> Exp -> Exp
fvarsOp op = go 0
  where go n (FVar i) = maybe (FVar i) (wkExp n) $ op i
        go n (a :-> b) = go n a :-> go (n + 1) b
        go n (Lam a b) = Lam (go n a) (go (n + 1) b)
        go n (f :#: x) = go n f :#: go n x
        go _ e = e

liftExp :: Int -> Int -> Exp -> Exp
liftExp d n = bvarsOp aux d
  where aux d' i = if d' <= i then BVar (n + i) else BVar i

wkExp :: Int -> Exp -> Exp
wkExp = liftExp 0

substIx :: Int -> Exp -> Exp -> Exp
substIx d v = bvarsOp aux d
  where aux d' i = case compare d' i of LT -> BVar (i - 1)
                                        EQ -> wkExp d' v
                                        GT -> BVar i

substEnv :: (String |-> Exp) -> Exp -> Exp
substEnv m = fvarsOp (`M.lookup` m)

substName :: String -> Exp -> Exp -> Exp
substName s e = fvarsOp (\i -> if i == s then Just e else Nothing)

rename :: (String,String) -> Exp -> Exp
rename (s1,s2) = substName s1 (FVar s2)
