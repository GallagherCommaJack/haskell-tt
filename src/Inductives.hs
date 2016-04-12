{-# LANGUAGE FlexibleContexts    #-}
{-# LANGUAGE FlexibleInstances   #-}
{-# LANGUAGE NoImplicitPrelude   #-}
{-# LANGUAGE OverloadedLists     #-}
{-# LANGUAGE OverloadedStrings   #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies        #-}
{-# LANGUAGE TypeOperators       #-}
{-# LANGUAGE UnicodeSyntax       #-}

module Inductives where
import           Data.ChunkedZip
import qualified Data.Foldable   as F
import           Exp
import           GHC.Exts        (IsList, Item)
import           Util

data Inductive = Ind {name    :: Name,
                      level   :: Int,
                      params  :: Vector (Name,Exp),
                      indices :: Vector Exp,
                      constrs :: Name |-> Exp}
               deriving (Read, Eq)

showParam :: Name -> Exp -> Text
showParam n e = "(" <> n <> " : " <> tshow e <> ")"

scanr :: (MonoFoldable t, IsSequence s) => (Element t -> Element s -> Element s)
                                        -> Element s
                                        -> t -> s
scanr f nil = snd . foldr (\a (b,bs) -> (f a b, f a b `cons` bs)) (nil,mempty)

scanl :: (MonoFoldable a, SemiSequence b, Monoid b) =>
        (Element b -> Element a -> Element b) -> Element b -> a -> b
scanl f nil = snd . foldl' (\(b,bs) a -> (f b a, bs `snoc` f b a)) (nil,mempty)

indent :: Int -> Text -> Text
indent 0 = id
indent n = ("  " <>) . indent (n - 1)

showConstructor :: Name -> Exp -> Text
showConstructor n e = n <> " : " <> tshow e

instance Show Inductive where
    show (Ind n l ps is cs) = unpack $
        "data " <> n <> " " <> fold (intersperse " " $ uncurry showParam <$> ps)
                <> " : " <> tshow (mkImpl is (Set l)) <> "\n"
        <> unlines (indent 1 <$> uncurry showConstructor <$> mapToList cs)

-- this is terrible but it'll have to do for now
asSeq :: Seq a -> Seq a
asSeq = id

isCorrectOrder :: (IsSet s, Monoid (ContainerKey s)) =>
                 Vector (ContainerKey s, s) -> Bool
isCorrectOrder ns = all (\(n,s) -> not (n `member` s)) $
                    asSeq $ scanl (\(_,s1) (n2,s2) -> (n2, s1 <> s2))
                                  (mempty,mempty)
                                  ns

freeInExp :: Name -> Exp -> Bool
freeInExp s (FVar i) = s == i
freeInExp s (a :-> b) = freeInExp s a || freeInExp s b
freeInExp s (Lam a b) = freeInExp s a || freeInExp s b
freeInExp s (f :#: x) = freeInExp s f || freeInExp s x
freeInExp _ _ = False

isPositive :: Name -> Exp -> Bool
isPositive s ((a :-> b) :-> t) = not (freeInExp s a) && isPositive s b && isPositive s t
isPositive s (Lam a b) = isPositive s a && isPositive s b
isPositive s (f :#: x) = isPositive s f && isPositive s x
isPositive _ _ = True

isValidInductive :: Inductive -> Bool
isValidInductive (Ind t n ps is cs) = isCorrectOrder ((t, mempty) `cons` fmap (second $ asHashSet . allFVars) ps)
                                      && all (<= n) (maxLevel <$> cs) && all (<= n) (maxLevel <$> is)
                                      && all (<= n) (maxLevel <$> snd <$> ps)
                                      && all (not . freeInExp t) is
                                      && all ((&&) <$> isPositive t <*> isConstrOf t) cs

enumToFrom :: Enum e => e -> e -> [e]
enumToFrom u l = [u, pred u..l]

-- mkCaseType :: (iName,cName) -> predicate -> type -> type
mkCaseType :: (Name,Name) -> Exp -> Exp -> Exp
mkCaseType (t,c) = go (asSeq [])
       where go m p (a :-> b) = let (xs,k) = first asSeq $ destrImpl a in
                                if isAppOf t k
                                then a :-> mkImpl (wkExp 1 <$> xs)
                                                  (wkExp 1 p :#:
                                                   mkApp (BVar (length xs)) (asVector $ BVar <$> reverse [0..length xs - 1]))
                                                         -- mkApp (BVar (length xs))
                                                         --       (BVar <$> reverse [0..length xs - 1]))
                                       :-> go (1 `cons` fmap (2+) m) (wkExp 2 p) b
                                else a :-> go (0 `cons` fmap (1+) m) (wkExp 1 p) b
             go m p k = if isAppOf t k
                        then p :#: mkApp (FVar c) (BVar <$> reverse m)
                        else k

newtype Triple a = Triple {getTriple :: (a,a,a)}

type instance Element (Triple a) = a

instance Foldable Triple where
    foldMap f (Triple (a1,a2,a3)) = f a1 ++ f a2 ++ f a3

instance MonoFoldable (Triple a) where
    ofoldMap f (Triple (a1,a2,a3)) = f a1 ++ f a2 ++ f a3

instance (Ord a) => MonoFoldableOrd (Triple a) where
    maximumEx (Triple (a1,a2,a3)) = maximumEx $ asVector [a1,a2,a3]

inferLevel :: Name -> Vector (Name,Exp) -> Vector Exp -> (Name |-> Exp) -> Inductive
inferLevel n p i c = Ind n lev p i c
    where lp = fromMaybe 0 $ maximumMay $ maxLevel <$> snd <$> p
          li = fromMaybe 0 $ maximumMay $ maxLevel <$> i
          lc = fromMaybe 0 $ maximumMay $ maxLevel <$> c
          lev = maximumEx $ Triple (lp,li,lc)

mapWithIx :: (IsList (f Int), Item (f Int) ~ Int) =>
            (Element (f Int) ~ Int, IsSequence (f Int), Zip f, MonoFoldable (f b)) =>
            (Int -> b -> c) -> f b -> f c
mapWithIx f xs = zipWith f (fromList [0..length xs]) xs

-- converts a (sorted) map of strings to types into a list of types suitable for use with mkImpl
--mkParams :: (Foldable f, Name,Exp), IsSequence o, Element o ~ Exp) =>
--           f -> o

-- this seems a little excessive
mkParams :: (MonoFoldable t, Element t ~ (Name,Exp)) => t -> [Exp]
mkParams = foldr (\(s,e) b -> e `cons` mapWithIx (substName s . BVar) b) mempty

mkRecType :: Inductive -> Exp -> Exp
mkRecType i@(Ind t _ ps is cs) p = assert (isValidInductive i) $
  mkImpl (ps' ++ cs' ++ is) (mkApp (FVar t) (asVector ixs) :-> p :#: BVar 0)
       where ps' = fromList $ mkParams ps
             psMap = mapFromList $ toList $ zip (fst <$> ps) [0..length ps]
             cs' = fromList $ mapWithIx (\n -> substEnv (BVar <$> (+n) <$> psMap))
                            $ (\(c,e) -> mkCaseType (t,c) p e) <$> mapToList cs
             ixs = reverse $ BVar <$> [0..length is - 1] ++ [length is + length cs' .. length ps' + length is + length cs' - 1]


wtype :: Int -> Int -> Inductive
wtype n m = inferLevel "W" [("A", Set n), ("B", "A" :-> Set m)] []
            [("sup", "A" :-> ("B" :#: BVar 0 :-> "W" :#: "A" :#: "B")
                         :-> "W" :#: "A" :#: "B")]

nat :: Inductive
nat = inferLevel "Nat" [] [] [("Z", "Nat"), ("S", "Nat" :-> "Nat")]

vec :: Inductive
vec = inferLevel "Vec" [("A", Set 0)] [FVar "Nat"]
      [("nil","Vec" :#: "A" :#: "Z"),
       ("cons", "Nat" :-> "A" :-> "Vec" :#: "A" :#: BVar 1 :-> "Vec" :#: "A" :#: ("S" :#: BVar 2))]

bad :: Inductive
bad = inferLevel "Wrong" [("A",FVar "B"), ("B",FVar "C"), ("C",FVar"A")] [] []

true :: Inductive
true = inferLevel "True" [] [] [("tt", "True")]

false :: Inductive
false = inferLevel "False" [] [] []

santa :: Inductive
santa = inferLevel "Curry" [] [] [("Santa", ("Santa" :-> "False") :-> "Santa")]

beq :: Inductive
beq = inferLevel "BEq"[("A",Set 0)] ["A","A"] [("refl","A" :-> "BEq" :#: 0 :#: 0)]

main :: IO ()
main = flip assert (putStrLn "All ok!") $ and (asSeq $ isValidInductive <$> (wtype <$> [0..10] <*> [0..10]))
                                        && isValidInductive vec
                                        && isValidInductive nat
                                        && isValidInductive true
                                        && isValidInductive false
                                        && not (isValidInductive bad)
                                        && not (isValidInductive santa)
-- --}
