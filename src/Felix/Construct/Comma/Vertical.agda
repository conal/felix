{-# OPTIONS --safe --without-K #-}

open import Level

open import Felix.Raw
open import Felix.Equiv
open import Felix.Laws as L hiding (Category; Cartesian)
open import Felix.Homomorphism
open ≈-Reasoning
open import Felix.Reasoning

module Felix.Construct.Comma.Vertical
   {o₀}{obj₀ : Set o₀} {ℓ₀} {_⇨₀_ : obj₀ → obj₀ → Set ℓ₀} ⦃ _ : Category _⇨₀_ ⦄
   {o₁}{obj₁ : Set o₁} {ℓ₁} {_⇨₁_ : obj₁ → obj₁ → Set ℓ₁} ⦃ _ : Category _⇨₁_ ⦄
   {o₂}{obj₂ : Set o₂} {ℓ₂} {_⇨₂_ : obj₂ → obj₂ → Set ℓ₂} ⦃ _ : Category _⇨₂_ ⦄
   {o₃}{obj₃ : Set o₃} {ℓ₃} {_⇨₃_ : obj₃ → obj₃ → Set ℓ₃} ⦃ _ : Category _⇨₃_ ⦄
   {q} ⦃ _ : Equivalent q _⇨₀_ ⦄ ⦃ _ : L.Category _⇨₀_ ⦄
   ⦃ _ : Homomorphismₒ obj₁ obj₀ ⦄ ⦃ _ : Homomorphism _⇨₁_ _⇨₀_ ⦄
     ⦃ catH₁ : CategoryH _⇨₁_ _⇨₀_ ⦄
   ⦃ _ : Homomorphismₒ obj₂ obj₀ ⦄ ⦃ _ : Homomorphism _⇨₂_ _⇨₀_ ⦄
     ⦃ catH₂ : CategoryH _⇨₂_ _⇨₀_ ⦄
   ⦃ _ : Homomorphismₒ obj₃ obj₀ ⦄ ⦃ _ : Homomorphism _⇨₃_ _⇨₀_ ⦄
     ⦃ catH₃ : CategoryH _⇨₃_ _⇨₀_ ⦄
 where

open import Felix.Construct.Comma.Type _⇨₀_ _⇨₁_ _⇨₂_ as A
open import Felix.Construct.Comma.Type _⇨₀_ _⇨₂_ _⇨₃_ as B
open import Felix.Construct.Comma.Type _⇨₀_ _⇨₁_ _⇨₃_ as C

open import Relation.Binary.PropositionalEquality using (_≡_; cong) renaming (sym to sym≡)

-- Vertical composition.
infixr 9 _◎_
_◎_ : ∀ {τ₁ τ₂ : obj₁} {τ₁′ τ₂′ : obj₂} {τ₁″ τ₂″ : obj₃}
        {h : Fₒ τ₁  ⇨₀ Fₒ τ₁′} {h′ : Fₒ τ₂  ⇨₀ Fₒ τ₂′}
        {k : Fₒ τ₁′ ⇨₀ Fₒ τ₁″} {k′ : Fₒ τ₂′ ⇨₀ Fₒ τ₂″}
        ((B.mk fₖ₁ _ _) : k B.⇉ k′) ((A.mk _ fₕ₂ _) : h A.⇉ h′) → ⦃ Fₘ fₖ₁ ≡ Fₘ fₕ₂ ⦄
    → k ∘ h C.⇉ k′ ∘ h′
_◎_ {h = h}{h′}{k}{k′} (B.mk fₖ₁ fₖ₂ is-g) (A.mk fₕ₁ fₕ₂ is-f) ⦃ eq ⦄ =
  C.mk fₕ₁ fₖ₂
    (begin
       (k′ ∘ h′) ∘ Fₘ fₕ₁
     ≈⟨ ∘-assocʳˡ′ is-f ⟩
       (k′ ∘ Fₘ fₕ₂) ∘ h
     ≡⟨ cong (λ z → (k′ ∘ z) ∘ h) (sym≡ eq) ⟩
       (k′ ∘ Fₘ fₖ₁) ∘ h
     ≈⟨ ∘≈ˡ is-g ⟩
       (Fₘ fₖ₂ ∘ k) ∘ h
     ≈⟨ ∘-assocʳ ⟩
       Fₘ fₖ₂ ∘ (k ∘ h)
     ∎)

-- Note that we could instead require the stronger condition fₖ₁ ≡ fₕ₂` or the
-- weaker condition `Fₘ fₖ₁ ≈ Fₘ fₕ₂`. With the latter alternative, I don't know
-- how to have the argument inferred.
