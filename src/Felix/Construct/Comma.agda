{-# OPTIONS --safe --without-K #-}

open import Level

open import Felix.Raw
open import Felix.Equiv
import Felix.Laws as L
open import Felix.Homomorphism

module Felix.Construct.Comma
   {o₀}{obj₀ : Set o₀} {ℓ₀} (_⇨₀_ : obj₀ → obj₀ → Set ℓ₀) ⦃ _ : Category _⇨₀_ ⦄
   {o₁}{obj₁ : Set o₁} {ℓ₁} (_⇨₁_ : obj₁ → obj₁ → Set ℓ₁) ⦃ _ : Category _⇨₁_ ⦄
   {o₂}{obj₂ : Set o₂} {ℓ₂} (_⇨₂_ : obj₂ → obj₂ → Set ℓ₂) ⦃ _ : Category _⇨₂_ ⦄
   {q₀} ⦃ _ : Equivalent q₀ _⇨₀_ ⦄ ⦃ _ : L.Category _⇨₀_ ⦄
   {q₁} ⦃ _ : Equivalent q₁ _⇨₁_ ⦄ -- ⦃ _ : L.Category _⇨₁_ ⦄
   {q₂} ⦃ _ : Equivalent q₂ _⇨₂_ ⦄ -- ⦃ _ : L.Category _⇨₂_ ⦄
   ⦃ hₒ₁ : Homomorphismₒ obj₁ obj₀ ⦄ ⦃ h₁ : Homomorphism _⇨₁_ _⇨₀_ ⦄
     ⦃ catH₁ : CategoryH _⇨₁_ _⇨₀_ ⦄
   ⦃ hₒ₂ : Homomorphismₒ obj₂ obj₀ ⦄ ⦃ h₂ : Homomorphism _⇨₂_ _⇨₀_ ⦄
     ⦃ catH₂ : CategoryH _⇨₂_ _⇨₀_ ⦄
 where

-- Comma.Type and Comma.Raw are re-exported by Comma.Homomorphism
open import Felix.Construct.Comma.Homomorphism _⇨₀_ _⇨₁_ _⇨₂_ public

