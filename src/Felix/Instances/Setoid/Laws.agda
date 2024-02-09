{-# OPTIONS --safe --without-K #-}

module Felix.Instances.Setoid.Laws where

open import Data.Product using (_,_; <_,_>; curry; uncurry)
open import Data.Unit.Polymorphic using (tt)
open import Function using (_∘_; _∘₂_; mk⇔)
open import Level using (_⊔_)
open import Relation.Binary using (Setoid)

open import Felix.Equiv using (Equivalent)
open import Felix.Raw as Raw
  hiding (Category; Cartesian; CartesianClosed; _∘_; curry; uncurry)
open import Felix.Laws using (Category; Cartesian; CartesianClosed)

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
    ; ∀× = λ {A} {B} {C} {f} {g} {k} → mk⇔
      < cong (exl {a = B} {b = C}) ∘_
      , cong (exr {a = B} {b = C}) ∘_
      >
      (uncurry <_,_>)
    -- this is _▵_ in category of functions and types,
    -- but I have trouble hinting to agda what Level it should use
    ; ▵≈ = <_,_>
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
