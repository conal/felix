{-# OPTIONS --safe --without-K #-}

open import Level

module Felix.Instances.Function.Type (ℓ : Level) where

import Data.Empty.Polymorphic as ⊥
import Data.Sum as ⊎
import Data.Unit as ⊤
open import Data.Unit.Polymorphic using () renaming (⊤ to ⊤′)
open import Data.Product using (_,_) renaming (_×_ to _×̇_)
open import Data.Fin using (Fin)
open import Data.Fin.Patterns using (0F; 1F)

infixr 0 _⇾_
_⇾_ : Set ℓ → Set ℓ → Set ℓ
A ⇾ B = A → B

pattern tt = lift ⊤.tt

-- lift₁ : ∀ {a b} {A : Set a} {B : Set b} {a′ b′}
--       → (A → B) → (Lift a′ A → Lift b′ B)
-- lift₁ f (lift x) = lift (f x)

-- lift₂ : ∀ {a b c} {A : Set a} {B : Set b} {C : Set c} {a′ b′ c′}
--       → (A → B → C) → (Lift a′ A → Lift b′ B → Lift c′ C)
-- lift₂ f (lift x) (lift y) = lift (f x y)

open import Function
open import Relation.Binary.PropositionalEquality
open ≡-Reasoning

-- Functions with left inverses are injective. TODO: maybe generalize to monic morphisms.
invertible-injective : ∀ {A B : Set ℓ} (f : A → B) (f⁻¹ : B → A) (f⁻¹∘f≗id : f⁻¹ ∘ f ≗ id) →
  ∀ {x y} → f x ≡ f y → x ≡ y
invertible-injective f f⁻¹ f⁻¹∘f≗id {x} {y} fx≡fy =
  begin
    x
  ≡⟨ sym (f⁻¹∘f≗id x) ⟩
    f⁻¹ (f x)
  ≡⟨ cong f⁻¹ fx≡fy ⟩
    f⁻¹ (f y)
  ≡⟨ f⁻¹∘f≗id y ⟩
    y
  ∎

module →-instances where

  open import Felix.Object

  instance

    products : Products (Set ℓ)
    products = record { ⊤ = ⊤′ ; _×_ = _×̇_ }

    coproducts : Coproducts (Set ℓ)
    coproducts = record { ⊥ = ⊥.⊥ ; _⊎_ = ⊎._⊎_ }

    exponentials : Exponentials (Set ℓ)
    exponentials = record { _⇛_ = _⇾_ }
