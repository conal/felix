{-# OPTIONS --safe --without-K #-}

module Felix.Instances.Setoid.Type where

open import Data.Empty.Polymorphic renaming (⊥ to ⊥′)
open import Data.Product.Relation.Binary.Pointwise.NonDependent using (×-setoid)
open import Data.Sum.Relation.Binary.Pointwise using (⊎-setoid)
open import Data.Unit.Polymorphic renaming (⊤ to ⊤′)
open import Function using (Func)
open import Function.Construct.Setoid renaming (setoid to ⟶-setoid)
open import Level using (Level; _⊔_)
open import Relation.Binary using (Setoid)

private
  variable
    a b ℓ₁ ℓ₂ : Level

infixr 0 _⟶_
_⟶_ : Setoid a ℓ₁ → Setoid b ℓ₂ → Set (a ⊔ b ⊔ ℓ₁ ⊔ ℓ₂)
_⟶_ = Func

open Func using (cong) public

infixl 5 _⟨$⟩_
_⟨$⟩_ : ∀ {c ℓ} → ∀ {A B : Setoid c ℓ} →
  A ⟶ B → Setoid.Carrier A → Setoid.Carrier B
_⟨$⟩_ = Func.to

module setoid-instances {c ℓ} where
  open import Felix.Object using (Coproducts; Exponentials; Products)

  instance
    products : Products (Setoid c ℓ)
    products = record
      { ⊤ = record
        { Carrier = ⊤′
        ; _≈_ = λ _ _ → ⊤′
        }
      ; _×_ = ×-setoid
      }

    coproducts : Coproducts (Setoid c (c ⊔ ℓ))
    coproducts = record
      { ⊥ = record
        { Carrier = ⊥′
        ; _≈_ = λ { () () }
        ; isEquivalence = record
          { refl = λ { {()} }
          ; sym = λ { {()} {()} _ }
          ; trans = λ { {()} {()} {()} _ _ }
          }
        }
      ; _⊎_ = ⊎-setoid
      }

    exponentials : Exponentials (Setoid (c ⊔ ℓ) (c ⊔ ℓ))
    exponentials = record { _⇛_ = ⟶-setoid }
