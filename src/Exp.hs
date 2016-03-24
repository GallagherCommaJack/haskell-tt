{-# LANGUAGE DeriveGeneric       #-}
{-# LANGUAGE NoImplicitPrelude   #-}
{-# LANGUAGE OverloadedLists     #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies        #-}
{-# LANGUAGE TypeOperators       #-}
module Exp where
import           Util

type Name = Text

-- uses a locally nameless approach
data Exp = Set Int | Exp :-> Exp
         | FVar Name | BVar  Int
         | Lam  Exp Exp  | Exp :#: Exp
         deriving (Read, Eq, Generic)

instance Hashable Exp

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
  show (FVar s) = unpack s
  show (BVar n) = show n
  show (Lam a b) = "λ " ++ show a ++ ". " ++ show b
  show (f :#: x) | isAtomic x = show f ++ " " ++ show x
                 | otherwise  = show f ++ " (" ++ show x ++ ")"

-- only there so we can define fromInteger
instance Num Exp where
  fromInteger = BVar . fromInteger
  a + b = error $ "Tried to add expression " ++ show a ++ " to " ++ show b
  a * b = error $ "Tried to multiply expression " ++ show a ++ " with " ++ show b
  negate a = error $ "Tried to negate expression " ++ show a
  abs a = error $ "Tried to take abs of expression " ++ show a
  signum a = error $ "Tried to get sign of expression " ++ show a

instance IsString Exp where
  fromString = FVar . pack

bvarsOp :: (Int -> Int -> Exp) -> Int -> Exp -> Exp
bvarsOp op d (BVar i) = op d i
bvarsOp op d (a :-> b) = bvarsOp op d a :-> bvarsOp op (d + 1) b
bvarsOp op d (Lam a b) = Lam (bvarsOp op d a) (bvarsOp op (d + 1) b)
bvarsOp op d (f :#: x) = bvarsOp op d f :#: bvarsOp op d x
bvarsOp _ _ e = e

fvarsOp :: (Name -> Maybe Exp) -> Exp -> Exp
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

substIxs :: Vector Exp -> Int -> Exp -> Exp
substIxs vs = bvarsOp aux
  where aux d i | i < d                        = BVar i
                | {- d <= -} i < d + length vs = maybe (BVar i) (wkExp i) $ vs !! (i - d)
                | otherwise                    = BVar $ i - length vs

substIx :: Int -> Exp -> Exp -> Exp
substIx d v = substIxs (singleton v) d

substEnv :: (Name |-> Exp) -> Exp -> Exp
substEnv m = fvarsOp (`lookup` m)

substName :: Name -> Exp -> Exp -> Exp
substName s e = fvarsOp (\i -> if i == s then Just e else Nothing)

rename :: (Name,Name) -> Exp -> Exp
rename (s1,s2) = substName s1 (FVar s2)

destrApp :: (SemiSequence s, Monoid s, Element s ~ Exp) =>
           Exp -> (Exp,s)
destrApp = second reverse . go
    where go (f :#: x) = second (cons x) $ destrApp f
          go k = (k,mempty)

destrImpl :: (SemiSequence s, Monoid s, Element s ~ Exp) =>
            Exp -> (s,Exp)
destrImpl (a :-> b) = first (cons a) $ destrImpl b
destrImpl k = (mempty,k)

destrLam :: (SemiSequence s, Monoid s, Element s ~ Exp) =>
           Exp -> (s,Exp)
destrLam (Lam a b) = first (cons a) $ destrLam b
destrLam e = (mempty,e)

mkImpl :: (MonoFoldable t, Element t ~ Exp) => t -> Exp -> Exp
mkImpl = flip $ foldr (:->)

mkApp :: (MonoFoldable t, Element t ~ Exp) => Exp -> t -> Exp
mkApp = foldl' (:#:)

mkLam :: (MonoFoldable t, Element t ~ Exp) => t -> Exp -> Exp
mkLam = flip $ foldr Lam

checkHead :: (Exp -> Bool) -> Exp -> Bool
checkHead p = p . fst . second asList . destrApp

isAppOf :: Name -> Exp -> Bool
isAppOf = checkHead . (==) . FVar

checkCodomain :: (Exp -> Bool) -> Exp -> Bool
checkCodomain p = p . snd . first asList . destrImpl

isConstrOf :: Name -> Exp -> Bool
isConstrOf = checkCodomain . isAppOf

checkBody :: (Exp -> Bool) -> Exp -> Bool
checkBody p = p . snd . first asList . destrLam

maxLevel :: Exp -> Int
maxLevel e = go 0 e id
  where go n (Set m)   cc = cc $ max n m
        go n (a :-> b) cc = go n a $ \m -> go m b cc
        go n (Lam a b) cc = go n a $ \m -> go m b cc
        go n (f :#: x) cc = go n f $ \m -> go m x cc
        go n _ _ = n

allFVars :: (IsSet s, Element s ~ Name) => Exp -> s
allFVars (a :-> b) = allFVars a <> allFVars b
allFVars (Lam a b) = allFVars a <> allFVars b
allFVars (FVar i) = singletonSet i
allFVars _ = mempty

