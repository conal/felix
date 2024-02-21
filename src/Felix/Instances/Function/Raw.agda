{-# OPTIONS --safe --without-K #-}

open import Level

module Felix.Instances.Function.Raw (ℓ : Level) where

import Function as F
open import Data.Product as × using (_,_; proj₁; proj₂; <_,_>; ∃; ∃₂)
open import Data.Sum as ⊎ using (inj₁; inj₂; [_,_])

open import Felix.Raw
open import Felix.Equiv

open import Felix.Instances.Function.Type ℓ public

module →-raw-instances where instance

  category : Category _⇾_
  category = record { id = F.id ; _∘_ = F._∘′_ }

  cartesian : Cartesian _⇾_
  cartesian = record { _▵_ = <_,_> ; exl = proj₁ ; exr = proj₂ }

  cocartesian : Cocartesian _⇾_
  cocartesian = record { ¡ = λ () ; _▿_ = [_,_] ; inl = inj₁ ; inr = inj₂ }

  distributive : Distributive _⇾_
  distributive = record
    { distribˡ⁻¹ = λ (a , bc) → ⊎.map (a ,_) (a ,_) bc
    ; distribʳ⁻¹ = λ (bc , a) → ⊎.map (_, a) (_, a) bc
    }

  traced : Traced _⇾_
  traced = record
    { WF = λ {a} {s} {b} f → ∀ (x : a) → ∃₂ λ (y : b) (z : s) → f (x , z) ≡ (y , z)
    ; trace = λ _ g → proj₁ F.∘ g
    } where open import Relation.Binary.PropositionalEquality

  cartesianClosed : CartesianClosed _⇾_
  cartesianClosed = record { curry = ×.curry ; apply = ×.uncurry id }

  open import Relation.Binary.PropositionalEquality as ≡ using (_≡_; _≗_)

  -- TODO: move to Relation.Binary.PropositionalEquality.Properties as a PR
  equivalent : Equivalent ℓ _⇾_
  equivalent = record
    { _≈_ = _≗_
    ; equiv = record
        { refl  = λ _ → ≡.refl
        ; sym   = λ f∼g x → ≡.sym (f∼g x)
        ; trans = λ f∼g g∼h x → ≡.trans (f∼g x) (g∼h x)
        }
    }
