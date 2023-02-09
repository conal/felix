{-# OPTIONS --safe --without-K #-}
-- Comma categories

open import Level

open import Felix.Raw
open import Felix.Equiv
open import Felix.Homomorphism

module Felix.Construct.Comma.Type
   {o₀}{obj₀ : Set o₀} {ℓ₀}(_⇨₀_ : obj₀ → obj₀ → Set ℓ₀) ⦃ c₀ : Category _⇨₀_ ⦄
   {o₁}{obj₁ : Set o₁} {ℓ₁}(_⇨₁_ : obj₁ → obj₁ → Set ℓ₁) ⦃ c₁ : Category _⇨₁_ ⦄
   {o₂}{obj₂ : Set o₂} {ℓ₂}(_⇨₂_ : obj₂ → obj₂ → Set ℓ₂) ⦃ c₂ : Category _⇨₂_ ⦄
   {q} ⦃ _ : Equivalent q _⇨₀_ ⦄
   ⦃ hₒ₁ : Homomorphismₒ obj₁ obj₀ ⦄ ⦃ h₁ : Homomorphism _⇨₁_ _⇨₀_ ⦄
     ⦃ catH₁ : CategoryH _⇨₁_ _⇨₀_ ⦄
   ⦃ hₒ₂ : Homomorphismₒ obj₂ obj₀ ⦄ ⦃ h₂ : Homomorphism _⇨₂_ _⇨₀_ ⦄
     ⦃ catH₂ : CategoryH _⇨₂_ _⇨₀_ ⦄
 where

-- TODO: Define some bundles to reduce syntactic clutter.

record Obj : Set (o₁ ⊔ o₂ ⊔ ℓ₀) where
  constructor mkO
  field
    { τ₁ } : obj₁
    { τ₂ } : obj₂
    h : Fₒ τ₁ ⇨₀ Fₒ τ₂

open Obj

infix 0 _⇨_
record _⇨_ (a b : Obj) : Set (q ⊔ ℓ₁ ⊔ ℓ₂) where
  constructor mk
  field
    f₁ : τ₁ a ⇨₁ τ₁ b
    f₂ : τ₂ a ⇨₂ τ₂ b
    ↻  : h b ∘ Fₘ f₁ ≈ Fₘ f₂ ∘ h a

open _⇨_

-- Shorthand
infix 0 _⇉_
_⇉_ : ∀ {σ₁ τ₁ : obj₁}{σ₂ τ₂ : obj₂}
    → (Fₒ σ₁ ⇨₀ Fₒ σ₂) → (Fₒ τ₁ ⇨₀ Fₒ τ₂) → Set (ℓ₁ ⊔ ℓ₂ ⊔ q)
g ⇉ h = mkO g ⇨ mkO h

module comma-type-instances where

  instance
  
    -- Forgetful functors

    open import Data.Product using (_,_)
    open import Felix.Construct.Product _⇨₁_ _⇨₂_ renaming (Obj to Obj× ; _⇨_ to _⇨×_)
    
    Hₒ× : Homomorphismₒ Obj Obj×
    Hₒ× = record { Fₒ = λ (mkO {τ₁} {τ₂} _) → τ₁ , τ₂}

    H× : Homomorphism _⇨_ _⇨×_
    H× = record { Fₘ = λ (mk f₁ f₂ _) → f₁ , f₂ }
    
    -- "Domain functor"
    Hₒ₁ : Homomorphismₒ Obj obj₁
    Hₒ₁ = record { Fₒ = τ₁ }

    H₁ : Homomorphism _⇨_ _⇨₁_
    H₁ = record { Fₘ = _⇨_.f₁ }

    -- "Codomain functor"
    Hₒ₂ : Homomorphismₒ Obj obj₂
    Hₒ₂ = record { Fₒ = τ₂ }

    H₂ : Homomorphism _⇨_ _⇨₂_
    H₂ = record { Fₘ = _⇨_.f₂ }
