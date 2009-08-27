{-# LANGUAGE TypeOperators
           , GADTs
           , FlexibleInstances
           , CPP
           #-}
-------------------------------------------------------------------------------
-- |
-- Module      : Data.Type.Equality
-- Copyright   : (c) 2009, Erik Hesselink
-- License     : BSD3
--
-- Maintainer  : Erik Hesselink <hesselink@gmail.com>
-- Stability   : Experimental
--
-- Type equality, coercion/cast and other operations.
--
-------------------------------------------------------------------------------
module Data.Type.Equality 
  ( (:=:)(Refl)
  , sym
  , trans
  , subst
  
  , cong
  , cong2
  , cong3
  
  , coerce
  
  , EqT(eqT)
  , EqT2(eqT2)
  , EqT3(eqT3)
  ) where

import Prelude
#if __GLASGOW_HASKELL__ >= 609
               hiding (id, (.))
import Control.Category
#endif

-- | Type equality. A value of @a :=: b@ is a proof that types @a@ and
-- @b@ are equal. By pattern matching on @Refl@ this fact is
-- introduced to the type checker.
data a :=: b where
  Refl :: a :=: a

infix 4 :=:

-- | Any value is just shown as "Refl", but this cannot be derived for
-- a GADT, so it is defined here manually.
instance Show (a :=: b) where
  showsPrec _ Refl = showString "Refl"

-- | We can only read values if the result is @a :=: a@, not @a :=: b@
-- since that is not true, in general. We just parse the string
-- "Refl", optionally surrounded with parentheses, and return 'Refl'.
instance Read (a :=: a) where
  readsPrec _ = readParen False (\s -> [(Refl, r) | ("Refl", r) <- lex s])

#if __GLASGOW_HASKELL__ >= 609
instance Category (:=:) where
  id = Refl
  Refl . Refl = Refl
#endif

-- | Equality is symmetric.
sym :: a :=: b -> b :=: a
sym Refl = Refl

-- | Equality is transitive. This is the same as (>>>) from the 'Category'
-- instance, but also works in GHC 6.8.
trans :: a :=: b -> b :=: c -> a :=: c
trans Refl Refl = Refl

-- | Equality is substitutive. This is defined directly, but can also
-- be defined as 'coerce' '.' 'cong'.
subst :: a :=: b -> f a -> f b
subst Refl = id

-- | Equality is congruential.
cong :: a :=: b -> f a :=: f b
cong Refl = Refl

-- | Congruence for type constructors with two parameters.
cong2 :: a :=: b -> c :=: d -> f a c :=: f b d
cong2 Refl Refl = Refl

-- | Congruence for type constructors with three parameters.
cong3 :: a :=: a'-> b :=: b' -> c :=: c' -> f a b c :=: f a' b' c'
cong3 Refl Refl Refl = Refl

-- | Coerce a type to another using an equality proof.
coerce :: a :=: b -> a -> b
coerce Refl = id

-- | A type class for constructing equality proofs. This is as close
-- as we can get to decidable equality on types. Note that @f@ must be
-- a GADT to be able to define 'eqT'.
class EqT f where
  eqT :: f a -> f b -> Maybe (a :=: b)

-- | A type class for constructing equality proofs for type
-- constructor with two parameters. Can be useful when representing
-- relations between types.
class EqT2 f where
  eqT2 :: f a b -> f c d -> (Maybe (a :=: c), Maybe (b :=: d))

-- | A type class for constructing equality proofs for type
-- constructor with three parameters. If you find a use for this, let
-- me know.
class EqT3 f where
  eqT3 :: f a b c -> f a' b' c' -> (Maybe (a :=: a'), Maybe (b :=: b'), Maybe (c :=: c'))

instance EqT ((:=:) a) where
  eqT Refl Refl = Just Refl
