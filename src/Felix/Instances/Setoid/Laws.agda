{-# OPTIONS --safe --without-K #-}

module Felix.Instances.Setoid.Laws where

open import Data.Product using (_,_)
open import Data.Unit.Polymorphic using (tt)
open import Function using (mk⇔)
open import Level using (_⊔_)
open import Relation.Binary using (Setoid)

open import Felix.Equiv using (Equivalent)
open import Felix.Raw hiding (Category; Cartesian; CartesianClosed)
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
    { ∀⊤ = λ _ → tt
    ; ∀× = λ {A} {B} {C} {f} {g} {k} → mk⇔
      (λ k≈f▵g → (λ x → cong (exl {a = B} {b = C}) (k≈f▵g x))
               , (λ x → cong (exr {a = B} {b = C}) (k≈f▵g x)))
      (λ (exl∘k≈f , exr∘k≈g) x → exl∘k≈f x , exr∘k≈g x)
    ; ▵≈ = λ h≈k f≈g x → h≈k x , f≈g x
    }

  cartesianClosed :
    ∀ {c ℓ} →
    CartesianClosed
      ⦃ products {c ⊔ ℓ} {c ⊔ ℓ} ⦄ ⦃ exponentials {c} {ℓ} ⦄ _⟶_
      ⦃ raw = setoid-raw-instances.cartesianClosed {c} {ℓ} ⦄
  cartesianClosed = record
    { ∀⇛ = λ {_} {_} {C} → mk⇔
      (λ g≈curry-f (a , b) → Setoid.sym C (g≈curry-f a {b}))
      (λ f≈uncurry-g a → λ {b} → Setoid.sym C (f≈uncurry-g (a , b)))
    ; curry≈ = λ f≈g a → λ {b} → f≈g (a , b)
    }
