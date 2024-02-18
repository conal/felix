{-# OPTIONS --safe --without-K #-}

module Felix.Equiv where

open import Level
open import Function
open import Data.Product renaming (<_,_> to _▵_)
open import Relation.Binary using (Rel; IsEquivalence; Setoid)
import Relation.Binary.Reasoning.Setoid as SetoidR

private
  variable
    o ℓ o₁ ℓ₁ o₂ ℓ₂ o₃ ℓ₃ : Level
    obj : Set o
    a b : obj

record Equivalent q {obj : Set o} (_⇨_ : obj → obj → Set ℓ)
       : Set (o ⊔ ℓ ⊔ suc q) where
  infix 4 _≈_
  field
    _≈_ : Rel (a ⇨ b) q   -- (f g : a ⇨ b) → Set q
    equiv : IsEquivalence (_≈_ {a}{b})

  module Equiv {a b} where
    open IsEquivalence (equiv {a}{b}) public

  open Equiv

  ≈setoid : obj → obj → Setoid ℓ q
  ≈setoid a b = record { isEquivalence = equiv {a}{b} }

  module ≈-Reasoning {a b} where
    open SetoidR (≈setoid a b) public

    refl≈ : {f : a ⇨ b} → f ≈ f
    refl≈ = Equiv.refl

    sym≈ : {f g : a ⇨ b} → f ≈ g → g ≈ f
    sym≈ = Equiv.sym

    infixr 9 _•_
    _•_ : {f g h : a ⇨ b} (g≈h : g ≈ h) (f≈g : f ≈ g) → f ≈ h
    g≈h • f≈g = Equiv.trans f≈g g≈h

    infixr 1 _;_   -- unicode
    _;_ : {f g h : a ⇨ b} (f≈g : f ≈ g) (g≈h : g ≈ h) → f ≈ h
    _;_ = trans

open Equivalent ⦃ … ⦄ public

-- TODO: consider moving to Felix.Homomorphism.
record Homomorphismₒ (obj₁ : Set o₁) (obj₂ : Set o₂) : Set (o₁ ⊔ o₂) where
  field
    Fₒ : obj₁ → obj₂

open Homomorphismₒ ⦃ … ⦄ public

id-Hₒ : Homomorphismₒ obj obj
id-Hₒ = record { Fₒ = id }

infixr 9 _∘Hₒ_
_∘Hₒ_ : ∀ {obj₁ : Set o₁} {obj₂ : Set o₂} {obj₃ : Set o₃} →
  Homomorphismₒ obj₂ obj₃ → Homomorphismₒ obj₁ obj₂ →
  Homomorphismₒ obj₁ obj₃
record { Fₒ = Gₒ } ∘Hₒ record { Fₒ = Fₒ } = record { Fₒ = Gₒ ∘ Fₒ }

infixr 7 _▵Hₒ_
_▵Hₒ_ : ∀ {obj₁ : Set o₁} {obj₂ : Set o₂} {obj₃ : Set o₃} →
  Homomorphismₒ obj₁ obj₂ → Homomorphismₒ obj₁ obj₃ →
  Homomorphismₒ obj₁ (obj₂ × obj₃)
record { Fₒ = Fₒ } ▵Hₒ record { Fₒ = Gₒ } = record { Fₒ = Fₒ ▵ Gₒ }


record Homomorphism
  {obj₁ : Set o₁} (_⇨₁_ : obj₁ → obj₁ → Set ℓ₁)
  {obj₂ : Set o₂} (_⇨₂_ : obj₂ → obj₂ → Set ℓ₂)
  ⦃ Hₒ : Homomorphismₒ obj₁ obj₂ ⦄
  : Set (o₁ ⊔ ℓ₁ ⊔ o₂ ⊔ ℓ₂) where
  field
    Fₘ : (a ⇨₁ b) → (Fₒ a ⇨₂ Fₒ b)

open Homomorphism ⦃ … ⦄ public

id-H : {obj : Set o} {_⇨_ : obj → obj → Set ℓ} → Homomorphism _⇨_ _⇨_ ⦃ Hₒ = id-Hₒ ⦄
id-H = record { Fₘ = id }

infixr 9 _∘H_
_∘H_ : ∀
  {obj₁ : Set o₁} {_⇨₁_ : obj₁ → obj₁ → Set ℓ₁}
  {obj₂ : Set o₂} {_⇨₂_ : obj₂ → obj₂ → Set ℓ₂}
  {obj₃ : Set o₃} {_⇨₃_ : obj₃ → obj₃ → Set ℓ₃}
  ⦃ Hₒ₁₂ : Homomorphismₒ obj₁ obj₂ ⦄ ⦃ Hₒ₂₃ : Homomorphismₒ obj₂ obj₃ ⦄ →
  Homomorphism _⇨₂_ _⇨₃_ → Homomorphism _⇨₁_ _⇨₂_ →
  Homomorphism _⇨₁_ _⇨₃_ ⦃ Hₒ = Hₒ₂₃ ∘Hₒ Hₒ₁₂ ⦄
record { Fₘ = Gₘ } ∘H record { Fₘ = Fₘ } = record { Fₘ = Gₘ ∘ Fₘ }

infixr 7 _▵H_
_▵H_ : ∀
  {obj₁ : Set o₁} {_⇨₁_ : obj₁ → obj₁ → Set ℓ₁}
  {obj₂ : Set o₂} {_⇨₂_ : obj₂ → obj₂ → Set ℓ₂}
  {obj₃ : Set o₃} {_⇨₃_ : obj₃ → obj₃ → Set ℓ₃}
  ⦃ Hₒ₁₂ : Homomorphismₒ obj₁ obj₂ ⦄ ⦃ Hₒ₁₃ : Homomorphismₒ obj₁ obj₃ ⦄ →
  Homomorphism _⇨₁_ _⇨₂_ → Homomorphism _⇨₁_ _⇨₃_ →
  Homomorphism _⇨₁_ (λ (a₂ , a₃) (b₂ , b₃) → (a₂ ⇨₂ b₂) × (a₃ ⇨₃ b₃))
    ⦃ Hₒ = Hₒ₁₂ ▵Hₒ Hₒ₁₃ ⦄
record { Fₘ = Fₘ } ▵H record { Fₘ = Gₘ } = record { Fₘ = Fₘ ▵ Gₘ }

-- I should probably move ▵H elsewhere so I can leverage more.

import Relation.Binary.Construct.On as On

H-equiv : {obj₁ : Set o₁} {_⇨₁_ : obj₁ → obj₁ → Set ℓ₁}
          {obj₂ : Set o₂} {_⇨₂_ : obj₂ → obj₂ → Set ℓ₂}
          {q : Level} ⦃ _ : Equivalent q _⇨₂_ ⦄
          ⦃ Hₒ : Homomorphismₒ obj₁ obj₂ ⦄
          ⦃ H : Homomorphism _⇨₁_ _⇨₂_ ⦄
        → Equivalent q _⇨₁_
H-equiv = record { equiv = On.isEquivalence Fₘ equiv }
