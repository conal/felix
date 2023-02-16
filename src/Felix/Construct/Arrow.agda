-- Arrow categories. Specializes comma categories with identity functors.
{-# OPTIONS --safe --without-K #-}

open import Level

open import Felix.Raw
open import Felix.Equiv
open import Felix.Laws as L hiding (Category; Cartesian; CartesianClosed)
open import Felix.Homomorphism

module Felix.Construct.Arrow
   {o}{obj : Set o}
   {ℓ} (_↠_ : obj → obj → Set ℓ) ⦃ _ : Category _↠_ ⦄
   {q} ⦃ _ : Equivalent q _↠_ ⦄ ⦃ _ : L.Category _↠_ ⦄
 where

private
  instance

    Hₒ : Homomorphismₒ obj obj
    Hₒ = id-Hₒ

    H : Homomorphism _↠_ _↠_
    H = id-H

    catH : CategoryH _↠_ _↠_
    catH = id-CategoryH

    -- TODO: Replace Hₒ, H, etc by a bundle

open import Felix.Construct.Comma.Raw _↠_ _↠_ _↠_
              ⦃ catH₁ = catH ⦄ ⦃ catH₂ = catH ⦄ public


module arrow-products ⦃ p : Products obj ⦄ ⦃ c : Cartesian _↠_ ⦄ ⦃ lc : L.Cartesian _↠_ ⦄ where

  instance

    productsH : ProductsH obj _↠_
    productsH = id-ProductsH

    strongProductsH : StrongProductsH obj _↠_
    strongProductsH = id-StrongProductsH

    cartesianH : CartesianH _↠_ _↠_
    cartesianH = id-CartesianH

    -- booleanH : BooleanH obj _↠_
    -- booleanH = id-BooleanH

    -- strongBooleanH : StrongBooleanH obj _↠_
    -- strongBooleanH = id-StrongBooleanH


-- Transposition
_ᵀ : ∀ {a b} ((mk f₁ f₂ _) : a ↬ b) → (f₁ ⇉ f₂)
_ᵀ {mkO h} {mkO h′} (mk _ _ commute) = mk h h′ (sym commute)

open import Relation.Binary.PropositionalEquality using (_≡_; refl)

-- Vertical composition.
infixr 9 _◎_
_◎_ : ∀ {τ₁ τ₂ τ₃ : obj} {τ₁′ τ₂′ τ₃′ : obj}
        {h : τ₁ ↠ τ₂} {h′ : τ₁′ ↠ τ₂′}
        {k : τ₂ ↠ τ₃} {k′ : τ₂′ ↠ τ₃′}
        ((mk fₖ₁ _ _) : k ⇉ k′) ((mk _ fₕ₂ _) : h ⇉ h′) → ⦃ fₖ₁ ≡ fₕ₂ ⦄
    → k ∘ h ⇉ k′ ∘ h′
(G ◎ F) ⦃ refl ⦄ = (G ᵀ ∘ F ᵀ) ᵀ
