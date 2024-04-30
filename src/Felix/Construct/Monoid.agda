-- Construct a one-object category from a monoid
{-# OPTIONS --safe --without-K #-}

open import Level using (Level)
open import Algebra.Bundles

module Felix.Construct.Monoid {c ℓ} (M : Monoid c ℓ) where

import Data.Unit as U           -- Unit.Polymorphic?

module M = Monoid M
open M renaming (Carrier to X)

infix 0 _⇒_
record _⇒_ (_ _ : U.⊤) : Set c where
  constructor mk⇒
  field un⇒ : X
open _⇒_

module monoid-instances where instance

  import Felix.Raw as R
  open import Felix.Equiv
  import Felix.Laws as L

  category : R.Category _⇒_
  category = record { id = mk⇒ ε ; _∘_ = λ (mk⇒ x) (mk⇒ y) → mk⇒ (x ∙ y) }

  import Relation.Binary.Construct.On as On

  equivalent : Equivalent ℓ _⇒_
  equivalent = record { equiv = On.isEquivalence un⇒ M.isEquivalence }

  lawful-category : L.Category _⇒_
  lawful-category = record
    { identityˡ = identityˡ _
    ; identityʳ = identityʳ _
    ; assoc     = assoc _ _ _
    ; ∘≈        = ∙-cong
    }
