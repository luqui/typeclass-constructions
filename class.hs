{-# LANGUAGE ConstraintKinds, RankNTypes, MultiParamTypeClasses, FunctionalDependencies, DeriveFunctor, ScopedTypeVariables, FlexibleContexts, UndecidableInstances, PolyKinds, GADTs, FlexibleInstances, OverlappingInstances, TypeOperators, KindSignatures #-}

import qualified Data.Proxy as P
import Data.Monoid
import Data.Reflection
import Data.Functor.Identity

data Proxy a = Proxy

-- F-Algebra library
-- -----------------
newtype Algebra f a = Algebra { getAlgebra :: f a -> a }

newtype W s a = W { getW :: a }

class (Functor f) => FAlgebra f c | c -> f where
    toAlgebra :: (c a) => Proxy c -> Algebra f a

pairAlg :: (Functor f) => Algebra f a -> Algebra f b -> Algebra f (a,b)
pairAlg (Algebra fa) (Algebra fb) = Algebra $ \fab -> (fa (fmap fst fab), fb (fmap snd fab))

isoAlg :: (Functor f) => (a -> b) -> (b -> a) -> Algebra f a -> Algebra f b
isoAlg ab ba (Algebra f) = Algebra $ ab . f .fmap ba

mReify :: forall a r. a -> (forall s. (Reifies s a) => (forall b. b -> W s b) -> r) -> r
mReify a cont = reify a (\(P.Proxy :: P.Proxy s) -> cont (W :: forall b. b -> W s b))

wAlg :: forall f c a s. (Reifies s (Algebra f a), FAlgebra f c) => Proxy c -> Algebra f (W s a)
wAlg _ = isoAlg W getW (reflect (Proxy :: Proxy s))


data ((f :: * -> *) :+: (g :: * -> *)) a = InL (f a) | InR (g a)
    deriving (Functor)

-- Monoid support library
-- ----------------------
data MonoidF r 
    = MEmpty
    | MAppend r r
    deriving (Functor)

class AMonoid m where
    monoidAlg :: Algebra MonoidF m

instance FAlgebra MonoidF AMonoid where
    toAlgebra _ = monoidAlg

-- XXX questionable
instance AMonoid m => Monoid m where
    mempty = getAlgebra monoidAlg MEmpty
    mappend x y = getAlgebra monoidAlg (MAppend x y)

instance (Reifies s (Algebra MonoidF a)) => AMonoid (W s a) where
    monoidAlg = wAlg (Proxy :: Proxy Monoid)

instance FAlgebra MonoidF Monoid where
    toAlgebra _ = Algebra go
        where
        go MEmpty = mempty
        go (MAppend x y) = mappend x y

monoidT :: Proxy Monoid
monoidT = Proxy

-- instances
plusMonoid :: (Num a) => Algebra MonoidF a
plusMonoid = isoAlg getSum Sum (toAlgebra monoidT)

timesMonoid :: (Num a) => Algebra MonoidF a
timesMonoid = isoAlg getProduct Product (toAlgebra monoidT)

dualMonoid :: Algebra MonoidF a -> Algebra MonoidF a
dualMonoid alg = mReify alg $ \w -> isoAlg (getW . getDual) (Dual . w) (toAlgebra monoidT)

endoMonoid :: Algebra MonoidF (a -> a)
endoMonoid = isoAlg appEndo Endo (toAlgebra monoidT)

anyMonoid :: Algebra MonoidF Bool
anyMonoid = isoAlg getAny Any (toAlgebra monoidT)

allMonoid :: Algebra MonoidF Bool
allMonoid = isoAlg getAll All (toAlgebra monoidT)

-- ...

-- Num support library
-- -------------------
data NumF r 
    = Plus r r
    | Times r r 
    | Minus r r
    | Negate r
    | Abs r
    | Signum r
    | FromInteger Integer
    deriving (Functor)

class ANum a where
    numAlg :: Algebra NumF a

instance FAlgebra NumF ANum where
    toAlgebra _ = numAlg

instance ANum a => Num a where
    x + y         = getAlgebra numAlg (Plus x y)
    x * y         = getAlgebra numAlg (Times x y)
    x - y         = getAlgebra numAlg (Minus x y)
    negate x      = getAlgebra numAlg (Negate x)
    abs x         = getAlgebra numAlg (Abs x)
    signum x      = getAlgebra numAlg (Signum x)
    fromInteger i = getAlgebra numAlg (FromInteger i)

instance (Reifies s (Algebra NumF a)) => ANum (W s a) where
    numAlg = wAlg (Proxy :: Proxy Num)

instance FAlgebra NumF Num where
    toAlgebra _ = Algebra go
        where
        go (Plus x y)      = x + y
        go (Times x y)     = x * y
        go (Minus x y)     = x - y
        go (Negate x)      = negate x
        go (Abs x)         = abs x
        go (Signum x)      = signum x
        go (FromInteger i) = fromInteger i

numT :: Proxy Num
numT = Proxy

numInteger :: Algebra NumF Integer
numInteger = toAlgebra numT

-- Example Usage
-- -------------

-- composing instances
test :: (Integer, Integer)
test = mReify (pairAlg plusMonoid timesMonoid) $ \w -> getW $ w (3,3) `mappend` w (4,4)

-- multiple classes
test2 :: Integer
test2 = mReify plusMonoid $ \plus -> 
         mReify timesMonoid $ \times -> 
          getW $ times (getW $ plus 1 `mappend` plus 1) 
                     `mappend` 
                 times (getW $ plus 2 `mappend` plus 2)


