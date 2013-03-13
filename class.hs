{-# LANGUAGE ConstraintKinds, RankNTypes, MultiParamTypeClasses, FunctionalDependencies, DeriveFunctor, ScopedTypeVariables, FlexibleContexts, UndecidableInstances, PolyKinds, GADTs, FlexibleInstances, OverlappingInstances #-}

import qualified Data.Proxy as P
import Data.Monoid
import Data.Reflection

data Proxy a = Proxy

-- algebra library
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

-- monoid support library
data MonoidF r 
    = MEmpty
    | MAppend r r
    deriving (Functor)

class AMonoid m where
    monoidAlg :: Algebra MonoidF m

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

-- ...

-- example

data SumProduct a = SumProduct a a
    deriving (Show)

instance (Num a) => AMonoid (SumProduct a) where
    monoidAlg = isoAlg (\(a,b) -> SumProduct a b) (\(SumProduct a b) -> (a,b)) 
              $ pairAlg plusMonoid timesMonoid

sp :: a -> SumProduct a
sp x = SumProduct x x

test = sp 3 `mappend` sp 4
