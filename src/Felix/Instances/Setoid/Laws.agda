{-# OPTIONS --safe --without-K #-}

module Felix.Instances.Setoid.Laws where

open import Data.Product using (_,_; <_,_>; curry; uncurry)
open import Data.Product.Relation.Binary.Pointwise.NonDependent using (_×ₛ_)
open import Data.Sum using (inj₁; inj₂)
open import Data.Sum.Relation.Binary.Pointwise using (_⊎ₛ_)
open import Data.Unit.Polymorphic using (tt)
open import Function using (_∘_; _∘₂_; mk⇔)
open import Level using (_⊔_)
open import Relation.Binary using (Setoid)

open import Felix.Equiv using (Equivalent)
open import Felix.Raw as Raw
  hiding (Category; Cartesian; CartesianClosed; Distributive; _∘_; curry; uncurry)
open import Felix.Laws using (Category; Cartesian; CartesianClosed; Distributive)

open import Felix.Instances.Setoid.Raw public

module setoid-laws-instances where instance

  category : ∀ {c ℓ} → Category {obj = Setoid c ℓ} _⟶_
  category = record
    { identityˡ = λ {_} {B} _ → Setoid.refl B
    ; identityʳ = λ {_} {B} _ → Setoid.refl B
    ; assoc = λ {_} {_} {_} {D} _ → Setoid.refl D
    ; ∘≈ = λ { {_} {_} {C} {f = f} {k = k} h≈k f≈g x →
      Setoid.trans C (h≈k (f ⟨$⟩ x)) (cong k (f≈g x)) }
    }

  cartesian : ∀ {c ℓ} → Cartesian {obj = Setoid c ℓ} _⟶_
  cartesian {c} {ℓ} = record
    -- ! in category of function and types
    { ∀⊤ = λ _ → tt
    ; ∀× = λ {A} {B} {C} → mk⇔
      < cong (exl {a = B} {b = C}) ∘_
      , cong (exr {a = B} {b = C}) ∘_
      >
      (uncurry <_,_>)
    -- this is _▵_ in category of functions and types,
    -- but I have trouble hinting to agda what Level it should use
    ; ▵≈ = <_,_>
    }

  distributive :
    ∀ {c ℓ} →
    Distributive
      ⦃ products {c} {c ⊔ ℓ} ⦄ ⦃ coproducts {c} {ℓ} ⦄
      _⟶_
      ⦃ raw = setoid-raw-instances.distributive {c} {ℓ} ⦄
  distributive = record
    { distribˡ∘distribˡ⁻¹ = λ where
      {A} {B} {C} (_ , inj₁ _) → Setoid.refl (A ×ₛ (B ⊎ₛ C))
      {A} {B} {C} (_ , inj₂ _) → Setoid.refl (A ×ₛ (B ⊎ₛ C))
    ; distribˡ⁻¹∘distribˡ = λ where
      {A} {B} {C} (inj₁ _) → Setoid.refl ((A ×ₛ B) ⊎ₛ (A ×ₛ C))
      {A} {B} {C} (inj₂ _) → Setoid.refl ((A ×ₛ B) ⊎ₛ (A ×ₛ C))
    ; distribʳ∘distribʳ⁻¹ = λ where
      {A} {B} {C} (inj₁ _ , _) → Setoid.refl ((B ⊎ₛ C) ×ₛ A)
      {A} {B} {C} (inj₂ _ , _) → Setoid.refl ((B ⊎ₛ C) ×ₛ A)
    ; distribʳ⁻¹∘distribʳ = λ where
      {A} {B} {C} (inj₁ _) → Setoid.refl ((B ×ₛ A) ⊎ₛ (C ×ₛ A))
      {A} {B} {C} (inj₂ _) → Setoid.refl ((B ×ₛ A) ⊎ₛ (C ×ₛ A))
    }

  cartesianClosed :
    ∀ {c ℓ} →
    CartesianClosed
      ⦃ products {c ⊔ ℓ} {c ⊔ ℓ} ⦄ ⦃ exponentials {c} {ℓ} ⦄ _⟶_
      ⦃ raw = setoid-raw-instances.cartesianClosed {c} {ℓ} ⦄
  cartesianClosed = record
    { ∀⇛ = λ {_} {_} {C} → mk⇔
      (λ g≈curry-f → Setoid.sym C ∘ uncurry g≈curry-f)
      (λ f≈uncurry-g → Setoid.sym C ∘₂ curry f≈uncurry-g)
    ; curry≈ = curry
    }
