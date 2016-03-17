{-# LANGUAGE OverloadedStrings   #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeOperators       #-}
{-# LANGUAGE UnicodeSyntax       #-}

module Inductive where
import           Control.Arrow
import           Control.Exception (assert)
import           Data.Bool
import           Data.Function
import qualified Data.Map          as M
import           Data.Maybe
import           Data.Monoid
import           Data.Set          (Set ())
import qualified Data.Set          as S
import           Exp

data Inductive = Ind {name    :: String,
                      params  :: String |-> Exp,
                      indices :: [Exp],
                      constrs :: String |-> Exp}
               deriving (Read, Show, Eq)

allFVars :: Exp -> Set String
allFVars (a :-> b) = allFVars a <> allFVars b
allFVars (Lam a b) = allFVars a <> allFVars b
allFVars (FVar i) = S.singleton i
allFVars _ = S.empty

noSelfRef :: String -> (String |-> Set String) -> Bool
noSelfRef s = not . getAny . M.foldMapWithKey (\k v -> Any (k `S.member` v || s `S.member` v))

-- need the generalized form to make sure that we have no circular dependencies
partitionA :: (Applicative m, Foldable f) => (a -> m Bool) -> f a -> m ([a],[a])
partitionA p = foldr (\a b -> bool (first (a:)) (second (a:)) <$> p a <*> b) $ pure ([],[])

sortByM :: (Monad m) => (a -> a -> m Bool) -> [a] -> m [a]
sortByM _ [] = pure []
sortByM cmp (x:xs) = do (l,r) <- partitionA (cmp x) xs
                        l' <- sortByM cmp l
                        r' <- sortByM cmp r
                        return (l' ++ [x] ++ r')

freeInExp :: String -> Exp -> Bool
freeInExp s (FVar i) = s == i
freeInExp s (a :-> b) = freeInExp s a || freeInExp s b
freeInExp s (Lam a b) = freeInExp s a || freeInExp s b
freeInExp s (f :#: x) = freeInExp s f || freeInExp s x
freeInExp _ _ = False

isPositive :: String -> Exp -> Bool
isPositive s ((a :-> b) :-> t) = not (freeInExp s a) && isPositive s b && isPositive s t
isPositive s (Lam a b) = isPositive s a && isPositive s b
isPositive s (f :#: x) = isPositive s f && isPositive s x
isPositive _ _ = True

destrApp :: Exp -> (Exp,[Exp])
destrApp (f :#: x) = second (++ [x]) $ destrApp f
destrApp k = (k,[])

checkHead :: (Exp -> Bool) -> Exp -> Bool
checkHead p = p . fst . destrApp

isAppOf :: String -> Exp -> Bool
isAppOf = checkHead . (==) . FVar

destrImpl :: Exp -> ([Exp],Exp)
destrImpl (a :-> b) = first (a:) $ destrImpl b
destrImpl k = ([],k)

checkCodomain :: (Exp -> Bool) -> Exp -> Bool
checkCodomain p = p . snd . destrImpl

isConstrOf :: String -> Exp -> Bool
isConstrOf = checkCodomain . isAppOf

isValidInductive :: Inductive -> Bool
isValidInductive (Ind t ps is cs) = all (not . freeInExp t) ps
                                    && noSelfRef t (allFVars <$> ps)
                                    && all (not . freeInExp t) is
                                    && all ((&&) <$> isPositive t <*> isConstrOf t) cs

mkImpl :: [Exp] -> Exp -> Exp
mkImpl = flip $ foldr (:->)

mkApp :: Exp -> [Exp] -> Exp
mkApp = foldl (:#:)

enumToFrom :: Enum e => e -> e -> [e]
enumToFrom u l = reverse [l..u]

-- mkCase :: (iName,cName) -> predicate -> type -> type
mkCase :: (String,String) -> Exp -> Exp -> Exp
mkCase (t,c) = go []
       where go m p (a :-> b) = let (xs,k) = destrImpl a in
                                if isAppOf t k
                                then a :-> mkImpl (wkExp 1 <$> xs)
                                                  (wkExp 1 p :#:
                                                         mkApp (BVar (length xs))
                                                               (BVar <$> reverse [0..length xs - 1]))
                                       :-> go (1 : fmap (2+) m) (wkExp 2 p) b
                                else a :-> go (0 : fmap (1+) m) (wkExp 1 p) b
             go m p k = if isAppOf t k
                        then p :#: mkApp (FVar c) (BVar <$> reverse m)
                        else k


mkInd :: String -> [(String,Exp)] -> [Exp] -> [(String,Exp)] -> Inductive
mkInd n p i c = Ind n (M.fromList p) i (M.fromList c)

wtype :: Int -> Int -> Inductive
wtype n m = mkInd "W" [("A", Set n), ("B", "A" :-> Set m)] []
                  [("sup", "A" :-> ("B" :#: BVar 0 :-> "W" :#: "A" :#: "B")
                               :-> "W" :#: "A" :#: "B")]

nat :: Inductive
nat = mkInd "Nat" [] [] [("Z", "Nat"), ("S", "Nat" :-> "Nat")]

compareParams :: (String,Set String) -> (String,Set String) -> Maybe Bool
compareParams (s1,e1) (s2,e2) = let c1 = s1 `S.member` e2
                                    c2 = s2 `S.member` e1
                                in if c1 && c2 then Nothing else Just c1

sortParams :: [(String,Exp)] -> Maybe [(String,Exp)]
sortParams = sortByM (compareParams `on` second allFVars)

mapWithIx :: (Int -> a -> b) -> [a] -> [b]
mapWithIx = flip zipWith [0..]

-- converts a (sorted) map of strings to types into a list of types suitable for use with mkImpl
mkParams :: [(String,Exp)] -> [Exp]
mkParams = foldr (\(s,e) b -> e : mapWithIx (substName s . BVar) b) []

mkRec :: Inductive -> Exp -> Exp
mkRec i@(Ind t ps is cs) p = assert (isValidInductive i) $ mkImpl (ps' ++ cs' ++ is) (mkApp (FVar t) ixs :-> p :#: BVar 0)
    where psList = fromJust $ sortParams $ M.toList ps
          psMap = M.fromList $ zip (fst <$> reverse psList) [0..]
          ps' = mkParams psList
          cs' = mapWithIx (\n -> substEnv (BVar <$> (+n) <$> psMap)) $ (\(c,e) -> mkCase (t,c) p e) <$> M.toList cs
          ixs = reverse $ BVar <$> [0..length is - 1] ++ [length (is ++ cs')..length (ps' ++ is ++ cs') - 1]

vec :: Inductive
vec = mkInd "Vec" [("A", Set 0)] [FVar "Nat"]
      [("nil","Vec" :#: "A" :#: "Z"),
       ("cons", "Nat" :-> "A" :-> "Vec" :#: "A" :#: BVar 1 :-> "Vec" :#: "A" :#: ("S" :#: BVar 2))]
