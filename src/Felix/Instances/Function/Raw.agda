{-# OPTIONS --safe --without-K #-}  -- K needed for Algebra.Indexed

open import Level

module Felix.Instances.Function.Raw (ℓ : Level) where

import Function as F
open import Data.Product as × using (_,_; proj₁; proj₂; <_,_>; ∃; ∃₂)
import Data.Bool as B

open import Felix.Raw
open import Felix.Equiv

open import Felix.Instances.Function.Type ℓ public

module →-raw-instances where instance

  category : Category _⇾_
  category = record { id = F.id ; _∘_ = F._∘′_ }

  cartesian : Cartesian _⇾_
  cartesian = record { _▵_ = <_,_> ; exl = proj₁ ; exr = proj₂ }

  -- indexedCartesian : ∀ {I : Set ℓ} → IndexedCartesian I _⇾_
  -- indexedCartesian = record
  --   { △  = λ fs x i → fs i x
  --   ; ex = λ i xs → xs i
  --   }

  traced : Traced _⇾_
  traced = record
    { WF = λ {a} {s} {b} f → ∀ (x : a) → ∃₂ λ (y : b) (z : s) → f (x , z) ≡ (y , z)
    ; trace = λ _ g → proj₁ F.∘ g
    } where open import Relation.Binary.PropositionalEquality

  cartesianClosed : CartesianClosed _⇾_
  cartesianClosed = record { curry = ×.curry ; apply = ×.uncurry id }

  -- logic : Logic _⇾_
  -- logic = record
  --           { false = λ tt → 𝕗
  --           ; true  = λ tt → 𝕥
  --           ; not   = lift₁ B.not
  --           ; ∧     = uncurry (lift₂ B._∧_)
  --           ; ∨     = uncurry (lift₂ B._∨_)
  --           ; xor   = uncurry (lift₂ B._xor_)
  --           ; cond  = λ (lift c , e , t) → B.if c then t else e
  --           }

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
