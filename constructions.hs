{-# LANGUAGE TupleSections, PolyKinds, ExistentialQuantification, RankNTypes, TypeOperators, DeriveFunctor, KindSignatures, ScopedTypeVariables #-}

import Control.Arrow
import Control.Comonad
import Control.Applicative
import Data.Traversable

type Algebra f a = f a -> a
type Coalgebra f a = a -> f a

pairAlg :: (Functor f) => Algebra f a -> Algebra f b -> Algebra f (a,b)
pairAlg alga algb = alga . fmap fst &&& algb . fmap snd

eitherCoalg :: (Functor f) => Coalgebra f a -> Coalgebra f b -> Coalgebra f (Either a b)
eitherCoalg coalga coalgb = fmap Left . coalga ||| fmap Right . coalgb


readerAlg :: (Functor f) => Algebra f a -> Algebra f (r -> a)
readerAlg alga f r = alga (fmap ($ r) f)

writerCoalg :: (Functor f) => Coalgebra f a -> Coalgebra f (w, a)
writerCoalg coalga (w,a) = fmap (w,) (coalga a)


newtype RealAlgebra f a = RA { getRA :: Algebra f a }
newtype RealCoalgebra f a = RC { getRC :: Coalgebra f a }

newtype ((f :: * -> *) :. (g :: * -> *)) x = Compose { getCompose :: f (g x) }
    deriving (Functor)

newtype Pi f = Pi { getPi :: forall a. f a }
data Sigma f = forall a. Sigma (f a)

piAlg :: (Functor f) => Pi (RealAlgebra f :. g) -> Algebra f (Pi g)
piAlg alg fpi = Pi (getRA (getCompose (getPi alg)) (fmap getPi fpi))

sigmaCoalg :: (Functor f) => Pi (RealCoalgebra f :. g) -> Coalgebra f (Sigma g)
sigmaCoalg coalg (Sigma gy) = fmap Sigma (getRC (getCompose (getPi coalg)) gy)


data ((f :: * -> *) :*: (g :: * -> *)) x = Pair { proj1 :: f x, proj2 :: g x }
    deriving (Functor)

data ((f :: * -> *) :+: (g :: * -> *)) x = InL (f x) | InR (g x)
    deriving (Functor)

coprodAlg :: Algebra f a -> Algebra g a -> Algebra (f :+: g) a
coprodAlg falg _ (InL fa) = falg fa
coprodAlg _ galg (InR ga) = galg ga

prodCoalg :: Coalgebra f a -> Coalgebra g a -> Coalgebra (f :*: g) a
prodCoalg fcoalg gcoalg a = Pair (fcoalg a) (gcoalg a)


prodAlg :: (Functor f, Functor g) 
        => Algebra f a -> Algebra g b -> Algebra (f :*: g) (a,b)
prodAlg falga galgb (Pair fab gab) = (falga (fmap fst fab), galgb (fmap snd gab))

coprodCoalg :: (Functor f, Functor g) 
            => Coalgebra f a -> Coalgebra g b -> Coalgebra (f :+: g) (Either a b)
coprodCoalg fcoalga _ (Left a) = InL (fmap Left (fcoalga a))
coprodCoalg _ gcoalgb (Right b) = InR (fmap Right (gcoalgb b))

-- unknown dual to pairCoalg
-- eitherAlg :: (Traversable f) => Algebra f a -> Algebra f b -> Algebra f (Either a b)

pairCoalg :: (Applicative f) => Coalgebra f a -> Coalgebra f b -> Coalgebra f (a,b)
pairCoalg coalga coalgb (a,b) = liftA2 (,) (coalga a) (coalgb b)


applicativeAlg :: (Traversable f, Applicative t) => Algebra f a -> Algebra f (t a)
applicativeAlg alg = fmap alg . sequenceA

traversableCoalg :: (Applicative f, Traversable t) => Coalgebra f a -> Coalgebra f (t a)
traversableCoalg coalg = sequenceA . fmap coalg


