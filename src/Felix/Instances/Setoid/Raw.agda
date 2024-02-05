{-# OPTIONS --safe --without-K  #-}

module Felix.Instances.Setoid.Raw where

open import Data.Product using (_,_; _,′_; curry′; uncurry′; ∃₂; proj₁; proj₂)
open import Data.Product.Function.NonDependent.Setoid using (<_,_>ₛ; proj₁ₛ; proj₂ₛ)
open import Data.Sum using ([_,_]; inj₁; inj₂)
open import Data.Sum.Function.Setoid using ([_,_]ₛ; inj₁ₛ; inj₂ₛ)
open import Data.Unit.Polymorphic using (tt)
open import Function using (Func) renaming (_∘_ to _∘ᵈ_)
open import Function.Construct.Composition as Comp
open import Function.Construct.Constant as Const
open import Function.Construct.Identity as Id
open import Level using (_⊔_; suc)
open import Relation.Binary using (Setoid)

open import Felix.Equiv using (Equivalent)
open import Felix.Raw
open import Felix.Instances.Setoid.Type
  using (module setoid-instances; _⟶_; cong; _⟨$⟩_) public
open setoid-instances public

module setoid-raw-instances where instance

  equivalent : ∀ {c ℓ} → Equivalent (c ⊔ ℓ) {obj = Setoid c ℓ} _⟶_
  equivalent = record
    { _≈_ = λ {From} {To} f g →
      let open Setoid To
      in ∀ x → f ⟨$⟩ x ≈ g ⟨$⟩ x
    ; equiv = λ {From} {To} →
      let open Setoid To
       in record
         { refl = λ _ → refl
         ; sym = λ f≈g x → sym (f≈g x)
         ; trans = λ f≈g g≈h x → trans (f≈g x) (g≈h x)
         }
    }

  category : ∀ {c ℓ} → Category {suc (c ⊔ ℓ)} {c ⊔ ℓ} {obj = Setoid c ℓ} _⟶_
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
  cocartesian {c} {ℓ} = record
    { ¡ = record
      { to = λ { () }
      ; cong = λ { {()} }
      }
    ; _▿_ = [_,_]ₛ
    ; inl = inj₁ₛ
    ; inr = inj₂ₛ
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
