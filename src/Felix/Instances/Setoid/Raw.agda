{-# OPTIONS --safe --without-K  #-}

module Felix.Instances.Setoid.Raw where

open import Data.Product using (_,_; _,′_; curry′; uncurry′; ∃₂; proj₁; proj₂)
open import Data.Product.Function.NonDependent.Setoid using (<_,_>ₛ; proj₁ₛ; proj₂ₛ)
open import Data.Sum using ([_,_]; inj₁; inj₂)
open import Data.Sum.Function.Setoid using ([_,_]ₛ; inj₁ₛ; inj₂ₛ)
open import Data.Sum.Relation.Binary.Pointwise using (inj₁; inj₂)
open import Data.Unit.Polymorphic using (tt)
open import Function using (Func) renaming (_∘_ to _∘ᵈ_)
open import Function.Construct.Composition as Comp
open import Function.Construct.Constant as Const
open import Function.Construct.Identity as Id
open import Level using (_⊔_; suc)
open import Relation.Binary using (Setoid)

open import Function.Construct.Setoid using (setoid)
open import Felix.Equiv using (Equivalent)
open import Felix.Raw
open import Felix.Instances.Setoid.Type
  using (module setoid-instances; _⟶_; cong; _⟨$⟩_) public

import Felix.Instances.Function as Fun

open setoid-instances public

module setoid-raw-instances where instance

  equivalent : ∀ {c ℓ} → Equivalent (c ⊔ ℓ) {obj = Setoid c ℓ} _⟶_
  equivalent = record
    { _≈_ = λ {From} {To} → Setoid._≈_ (setoid From To)
    ; equiv = λ {From} {To} → Setoid.isEquivalence (setoid From To)
    }

  category : ∀ {c ℓ} → Category {obj = Setoid c ℓ} _⟶_
  category = record
    { id = Id.function _
    -- flip′ Comp.function doesn't reduce in goals
    ; _∘_ = λ g f → Comp.function f g
    }

  cartesian : ∀ {c ℓ} → Cartesian {obj = Setoid c ℓ} _⟶_
  cartesian = record
    { ! = Const.function _ ⊤ tt
    ; _▵_ = <_,_>ₛ
    ; exl = proj₁ₛ
    ; exr = proj₂ₛ
    }

  cocartesian : ∀ {c ℓ} → Cocartesian ⦃ coproducts {c} {ℓ} ⦄ _⟶_
  cocartesian = record
    { ¡ = record
      { to = λ { () }
      ; cong = λ { {()} }
      }
    ; _▿_ = [_,_]ₛ
    ; inl = inj₁ₛ
    ; inr = inj₂ₛ
    }

  distributive :
    ∀ {c ℓ} →
    Distributive
      ⦃ products {c} {c ⊔ ℓ} ⦄ ⦃ coproducts {c} {ℓ} ⦄
      _⟶_
      ⦃ category {c} {c ⊔ ℓ} ⦄ ⦃ cartesian {c} {c ⊔ ℓ} ⦄ ⦃ cocartesian {c} {ℓ} ⦄
  distributive {c} {ℓ} = let open Fun c in record
    { distribˡ⁻¹ = record
      { to = distribˡ⁻¹
      ; cong = λ where
        (a₁≈a₂ , inj₁ b₁≈b₂) → inj₁ (a₁≈a₂ , b₁≈b₂)
        (a₁≈a₂ , inj₂ c₁≈c₂) → inj₂ (a₁≈a₂ , c₁≈c₂)
      }
    ; distribʳ⁻¹ = record
      { to = distribʳ⁻¹
      ; cong = λ where
        (inj₁ b₁≈b₂ , a₁≈a₂) → inj₁ (b₁≈b₂ , a₁≈a₂)
        (inj₂ c₁≈c₂ , a₁≈a₂) → inj₂ (c₁≈c₂ , a₁≈a₂)
      }
    }

  -- omit until I can be sure it's ok
  -- traced : ∀ {c ℓ} → Traced {obj = Setoid (c ⊔ ℓ) (c ⊔ ℓ)} _⟶_
  -- traced = record
  --   { WF = λ {_} {s} {b} f →
  --     let open Equivalent equivalent in
  --     ∃₂ λ (y : ⊤ ⟶ b) (z : ⊤ ⟶ s) →
  --     f ∘ constʳ z ≈ (y ⦂ z) ∘ !
  --   ; trace = λ { f (y , z , eq) → exl ∘ f ∘ constʳ z }
  --   }

  cartesianClosed :
    ∀ {c ℓ} →
    CartesianClosed ⦃ products {c ⊔ ℓ} {c ⊔ ℓ} ⦄ ⦃ exponentials {c} {ℓ} ⦄ _⟶_
  cartesianClosed = record
    { curry = λ {A} {B} f → record
      { to = λ a → record
        { to = curry′ (f ⟨$⟩_) a
        ; cong = curry′ (cong f) (Setoid.refl A)
        }
      ; cong = λ x≈y _ → cong f (x≈y , Setoid.refl B)
      }
    ; apply = λ {A} {B} → record
      { to = uncurry′ _⟨$⟩_
      ; cong = λ { {f , x} {g , y} (f≈g , x≈y) →
        Setoid.trans B (f≈g x) (cong g x≈y) }
      }
    }
