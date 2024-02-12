{-# OPTIONS --safe --without-K #-}

module Felix.All where

-- Temporary sanity check while finding a commit point in agda-stdlib that will
-- work with agda-2.6.3 and Felix and reflection (particularly the ring solver).
open import Data.Nat.Tactic.RingSolver using (solve-∀)

import Felix.Object
import Felix.Equiv
import Felix.Raw
import Felix.Laws
import Felix.Reasoning
import Felix.Homomorphism
import Felix.MakeLawful

import Felix.Prop
import Felix.Subcategory.Object
import Felix.Subcategory.Morphism

import Felix.Construct.Product
import Felix.Construct.Squared
import Felix.Construct.Comma
import Felix.Construct.Arrow

import Felix.Instances.Function
import Felix.Instances.Identity
