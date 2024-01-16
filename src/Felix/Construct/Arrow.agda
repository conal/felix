-- Arrow categories. Specializes comma categories with identity functors.
{-# OPTIONS --safe --without-K #-}

open import Level

open import Felix.Raw
open import Felix.Equiv as R
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
_ᵀ : ∀ {a b} ((mkᵐ f₁ f₂ _) : a ↬ b) → (f₁ ⇉ f₂)
_ᵀ {mkᵒ h} {mkᵒ h′} (mkᵐ _ _ commute) = mkᵐ h h′ (sym commute)

open import Relation.Binary.PropositionalEquality using (_≡_; refl)

-- Object composition
composableᵒ : Obj → Obj → Set o
composableᵒ (mkᵒ {τ₂′} {τ₃′} _) (mkᵒ {τ₁} {τ₂} _) = τ₂′ ≡ τ₂

infixr 9 _○_
_○_ : ∀ (a b : Obj) → ⦃ composableᵒ a b ⦄ → Obj
(mkᵒ g ○ mkᵒ f) ⦃ refl ⦄ = mkᵒ (g ∘ f)

-- Vertical morphism composition

vcomposable : ∀ {a₂ b₂ a₁ b₁} → ⦃ composableᵒ a₂ a₁ ⦄ → ⦃ composableᵒ b₂ b₁ ⦄ →
  (a₂ ↬ b₂) → (a₁ ↬ b₁) → Set ℓ
vcomposable ⦃ refl ⦄ ⦃ refl ⦄ (mkᵐ fₖ₂ fₕ₂ _) (mkᵐ fₖ₁ fₕ₁ _) = fₕ₁ ≡ fₖ₂
-- vcomposable ⦃ p@refl ⦄ ⦃ q@refl ⦄ (mkᵐ _ fₕ₂ _) (mkᵐ fₖ₁ _ _) = {!!}

infixr 9 _◎_
_◎_ : ∀ {a₂ b₂ a₁ b₁} → (G : a₂ ↬ b₂) (F : a₁ ↬ b₁)
  ⦃ cᵢ : composableᵒ a₂ a₁ ⦄ ⦃ cₒ : composableᵒ b₂ b₁ ⦄ ⦃ c : vcomposable G F ⦄ →
  a₂ ○ a₁ ↬ b₂ ○ b₁
(G ◎ F) ⦃ refl ⦄ ⦃ refl ⦄ ⦃ refl ⦄ = (G ᵀ ∘ F ᵀ) ᵀ

-- TODO: Generalize vertical composition to general comma categories.

Id : obj → Obj
Id a = mkᵒ (id {a = a})

idᵀ : ∀ {a b} → (a ↠ b) → Id a ↬ Id b
idᵀ f = id {a = mkᵒ f} ᵀ
-- idᵀ f = mkᵐ f f ...
