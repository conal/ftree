{-# LANGUAGE GADTs, KindSignatures, TypeOperators, Rank2Types, DataKinds #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# OPTIONS_GHC -Wall #-}

----------------------------------------------------------------------
-- |
-- Module      :  Data.FTree.TopDown
-- Copyright   :  (c) 2011 Conal Elliott
-- 
-- Maintainer  :  conal@conal.net
-- Stability   :  experimental
-- 
-- Top-down, depth-typed functor trees.
-- In other words, right-associated n-ary functor composition.
-- See <http://conal.net/blog/posts/a-trie-for-length-typed-vectors/>.
----------------------------------------------------------------------

module Data.FTree.TopDown (T(..),(:^),unL,unB,foldT,inT,inT2,inL,inB,inL2,inB2) where

-- TODO: explicit exports

import Prelude hiding (and)

import Control.Applicative (Applicative(..),liftA2,(<$>))
import Data.Foldable (Foldable(..),and)
import Data.Traversable (Traversable(..))
import Data.Monoid (Monoid(..))

import TypeUnary.Nat

import Text.ShowF

-- References:
--
-- [*Applicative Programming with Effects*]: http://www.soi.city.ac.uk/~ross/papers/Applicative.html
-- [*Semantic editor combinators*]: http://conal.net/blog/posts/semantic-editor-combinators/

-- Since composition is associative, a recursive formulation might naturally fold from the left or from the right.
-- In this module, we'll fold on the right
-- See the module `BottomUp` for left-folded composition.

--   f :^ Z   =~ Id
--   f :^ S n =~ f :. (f :^ n)

-- Writing as a GADT:

data T :: (* -> *) -> * -> (* -> *) where
  L :: a -> T f Z a
  B :: IsNat n => f (T f n a) -> T f (S n) a

type (:^) = T

unL :: (f :^ Z) a -> a
unL (L a) = a

unB :: (f :^ S n) a -> f ((f :^ n) a)
unB (B fsa) = fsa

foldT :: forall f n a z. Functor f =>
         (a -> z) -> (f z -> z) -> (f :^ n) a -> z
foldT l b = fo
 where
   fo :: (f :^ m) a -> z
   fo (L a)  = l a
   fo (B ts) = b (fo <$> ts)

-- Operate inside the representation of `f :^ n`:

inT :: (a -> b)
    -> (forall n. IsNat n => f ((f :^ n) a) -> f ((f :^ n) b))
    -> (forall n. (f :^ n) a -> (f :^ n) b)
inT l _ (L a ) = (L (l a ))
inT _ b (B as) = (B (b as))

inT2 :: (a -> b -> c)
     -> (forall n. IsNat n => f ((f :^ n) a) -> f ((f :^ n) b) -> f ((f :^ n) c))
     -> (forall n. (f :^ n) a -> (f :^ n) b -> (f :^ n) c)
inT2 l _ (L a ) (L b ) = L (l a  b )
inT2 _ b (B as) (B bs) = B (b as bs)
inT2 _ _ _ _ = error "inT2: unhandled case"  -- Possible??

-- Similar to `inT`, but useful when we can know whether a `L` or a `B`:

inL :: (a -> b)
        -> ((f :^ Z) a -> (f :^ Z) b)
inL h (L a ) = L (h a )

inB :: (f ((f :^ n) a) -> f ((f :^ n) b))
        -> ((f :^ (S n)) a -> (f :^ (S n)) b)
inB h (B as) = B (h as)

inL2 :: (a -> b -> c)
         -> ((f :^ Z) a -> (f :^ Z) b -> (f :^ Z) c)
inL2 h (L a ) (L b ) = L (h a  b )

inB2 :: (f ((f :^ n) a) -> f ((f :^ n) b) -> f ((f :^ n) c))
         -> ((f :^ (S n)) a -> (f :^ (S n)) b -> (f :^ (S n)) c)
inB2 h (B as) (B bs) = B (h as bs)


instance (ShowF f, Show a) => Show ((f :^ n) a) where show = showF

instance ShowF f => ShowF (f :^ n) where
  showsPrecF p (L a ) = showsApp1  "L" p a
  showsPrecF p (B as) = showsFApp1 "B" p as

-- Functors compose into functors and applicatives into applicatives.
-- (See [*Applicative Programming with Effects*] (section 5) and [*Semantic editor combinators*].)
-- The following definitions arise from the standard instances for binary functor composition.

instance Functor f => Functor (f :^ n) where
  fmap h = inT h ((fmap.fmap) h)

instance (IsNat n, Applicative f) => Applicative (f :^ n) where
  pure = pureN nat
  (<*>) = inT2 ($) (liftA2 (<*>))

pureN :: Applicative f => Nat n -> a -> (f :^ n) a
pureN Zero     a = L a
pureN (Succ _) a = B ((pure . pure) a)

-- More explicitly:

--   pureN (Succ n) a = B ((pure . pureN n) a)

-- The `Foldable` and `Traversable` classes are also closed under composition.

instance (Functor f, Foldable f) => Foldable (f :^ n) where
  fold (L a ) = a
  fold (B as) = fold (fold <$> as)

-- Alternatively, define `foldMap`:

--     foldMap h (L a ) = h a
--     foldMap h (B as) = fold (foldMap h <$> as)

-- Better yet:

  foldMap h (L a ) = h a
  foldMap h (B as) = (foldMap.foldMap) h as


instance Traversable f => Traversable (f :^ n) where
  sequenceA (L qa) = L <$> qa
  sequenceA (B as) = fmap B . sequenceA . fmap sequenceA $ as

-- i.e.,

--     sequenceA . L = fmap L
-- <
--     sequenceA . B = fmap B . sequenceA . fmap sequenceA

-- We can use the `Applicative` instance in standard way to get a `Monoid` instance:

instance (IsNat n, Applicative f, Monoid m) => Monoid ((f :^ n) m) where
  mempty  = pure mempty
  mappend = liftA2 mappend

-- (To follow the general pattern exactly, replace the first two constraints with `Applicative (f :^ n)` and add `FlexibleContexts` to the module's `LANGUAGE` pragma.)


-- Equality and ordering
-- =====================

-- Standard forms:

instance (Foldable f, Applicative f, IsNat n, Eq a) => Eq ((f :^ n) a) where
  (==) = (fmap.fmap) and (liftA2 (==))

instance (Foldable f, Applicative f, IsNat n, Ord a) => Ord ((f :^ n) a) where
  compare = (fmap.fmap) fold (liftA2 compare)
