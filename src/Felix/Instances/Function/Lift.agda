{-# OPTIONS --safe --without-K #-}

open import Level

module Felix.Instances.Function.Lift (a b : Level) where

open Lift
open import Data.Product using (_,_; uncurry)
open import Function using (_∘_)

open import Felix.Homomorphism
open import Felix.Object
import Felix.Instances.Function
open module F {ℓ} = Felix.Instances.Function ℓ

private
  variable
    A : Set a

lift₀′ : A → Lift b A
lift₀′ = lift

lift₀ : A → (⊤ ⇾ Lift b A)
lift₀ n tt = lift n

lift₁ : (A ⇾ A) → (Lift b A ⇾ Lift b A)
lift₁ f (lift a) = lift (f a)

lift₂′ : (A ⇾ A ⇾ A) → (Lift b A ⇾ Lift b A ⇾ Lift b A)
lift₂′ f (lift a) (lift b) = lift (f a b)

lift₂ : (A ⇾ A ⇾ A) → (Lift b A × Lift b A ⇾ Lift b A)
lift₂ = uncurry ∘ lift₂′

module function-lift-instances where instance

  Hₒ : Homomorphismₒ (Set a) (Set (a ⊔ b))
  Hₒ = record { Fₒ = Lift b }

  H : Homomorphism (_⇾_ {a}) (_⇾_ {a ⊔ b})
  H = record { Fₘ = λ { f (lift x) → lift (f x) } }

  open import Relation.Binary.PropositionalEquality

  catH : CategoryH (_⇾_ {a}) (_⇾_ {a ⊔ b})
  catH = record
    { F-cong = λ f≈g → λ (lift x) → cong lift (f≈g x)
    ; F-id = λ _ → refl
    ; F-∘  = λ _ → refl
    }

  pH : ProductsH (Set a) (_⇾_ {a ⊔ b})
  pH = record
    { ε   = λ { tt → lift tt }
    ; μ   = λ (lift x , lift y) → lift (x , y)
    ; ε⁻¹ = λ { (lift tt) → tt }
    ; μ⁻¹ = λ (lift (x , y)) → lift x , lift y }

  spH : StrongProductsH (Set a) (_⇾_ {a ⊔ b})
  spH = record
    { ε⁻¹∘ε = λ _ → refl
    ; ε∘ε⁻¹ = λ _ → refl
    ; μ⁻¹∘μ = λ _ → refl
    ; μ∘μ⁻¹ = λ _ → refl }

  cartH : CartesianH (_⇾_ {a}) (_⇾_ {a ⊔ b})
  cartH = record
     { F-!   = λ _ → refl
     ; F-▵   = λ _ → refl
     ; F-exl = λ _ → refl
     ; F-exr = λ _ → refl }
