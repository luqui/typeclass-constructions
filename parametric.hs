{-# LANGUAGE GADTs, RankNTypes, TypeOperators, PolyKinds, FlexibleInstances #-}

import Prelude hiding (id, (.))
import qualified Prelude
import Control.Applicative
import Control.Monad (join)

class Category c where
    id :: c x x
    (.) :: c y z -> c x y -> c x z

-- types & functions
instance Category (->) where
    id = Prelude.id
    (.) = (Prelude..)

-- functors & natural transformations
infixl 1 %
newtype f :~> g = NT { (%) :: forall x. f x -> g x }

instance Category (:~>) where
    id = NT id
    NT g . NT f = NT (g . f)

-- endofunctors in the category of [endofunctors on Hask]
class FFunctor f where
    ffmap :: (Functor a, Functor b) => (a :~> b) -> f a :~> f b

type Alg c f a = c (f a) a




data FunctorF f a where
    Fmap :: (a -> b) -> f a -> FunctorF f b

instance FFunctor FunctorF where
    ffmap t = NT $ \(Fmap f a) -> Fmap f (t % a)


functorAlg :: (Functor f) => Alg (:~>) FunctorF f
functorAlg = NT $ \(Fmap f t) -> fmap f t

data ApplicativeF f a where
    Pure :: a -> ApplicativeF f a
    Ap   :: f (a -> b) -> f a -> ApplicativeF f b

instance FFunctor ApplicativeF where
    ffmap t = NT $ \a -> case a of
        Pure x -> Pure x
        Ap f x -> Ap (t % f) (t % x)


applicativeAlg :: (Applicative f) => Alg (:~>) ApplicativeF f
applicativeAlg = NT $ \a -> case a of
    Pure x -> pure x
    Ap f x -> f <*> x

data MonadF f a where
    Return :: a -> MonadF f a
    Join   :: f (f a) -> MonadF f a

instance FFunctor MonadF where
    ffmap t = NT $ \a -> case a of
        Return x -> Return x
        Join mm  -> Join (t % (fmap (t %) mm))

monadAlg :: (Monad f) => Alg (:~>) MonadF f
monadAlg = NT $ \a -> case a of
    Return x -> return x
    Join mm  -> join mm



data FreeF f a x where
    FPure   :: a x -> FreeF f a x
    FEffect :: f (FreeF f a) x -> FreeF f a x


