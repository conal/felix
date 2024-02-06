{-# OPTIONS --safe --without-K #-}
open import Level using (Level; suc; _⊔_)

module Felix.Instances.Pred (m ℓm : Level) where

open import Data.Product using (_,_; ∃; proj₁)
open import Relation.Unary using (Pred; _⟨×⟩_; _⟨→⟩_)

open import Felix.Object
open import Felix.Raw
private module F {ℓ} where open import Felix.Instances.Function ℓ public
open F

-- Level-generalized U from Relation.Unary
U : ∀ {a ℓ} {A : Set a} → Pred A ℓ
U x = ⊤

record PRED : Set (suc (m ⊔ ℓm)) where
  constructor mkᵒ
  field
    {ty}  : Set m
    pred  : Pred ty ℓm

module PRED-objects where instance

  products : Products PRED
  products = record { ⊤ = mkᵒ {⊤} U ; _×_ = λ (mkᵒ P) (mkᵒ Q) → mkᵒ (P ⟨×⟩ Q) }

infix 0 _⇒_
record _⇒_ (𝒜 ℬ : PRED) : Set (m ⊔ ℓm) where
  constructor mkᵐ ; open PRED
  field
    {f}  : ty 𝒜 → ty ℬ
    imp  : (pred 𝒜 ⟨→⟩ pred ℬ) f

module PRED-morphisms where instance

  cat : Category _⇒_
  cat = record
    { id   = mkᵐ id
    ; _∘_  = λ (mkᵐ g) (mkᵐ f) → mkᵐ (g ∘ f) }

  cart : Cartesian _⇒_
  cart = record
    { !    = mkᵐ !
    ; _▵_  = λ (mkᵐ f) (mkᵐ g) → mkᵐ (f ▵ g)
    ; exl  = mkᵐ exl
    ; exr  = mkᵐ exr }

-- Project away the predicates and proofs
module PRED-functor where instance
  open import Felix.Homomorphism

  Hₒ : Homomorphismₒ PRED (Set m)
  Hₒ = record { Fₒ = PRED.ty }

  H : Homomorphism _⇒_ _⇾_
  H = record { Fₘ = _⇒_.f }

  catH : CategoryH _⇒_ _⇾_
  catH = record { F-id = refl ; F-∘ = refl }

  pH : ProductsH PRED _⇾_
  pH = record { ε = id ; μ = id ; ε⁻¹ = id ; μ⁻¹ = id }

  import Felix.Laws as L

  spH : StrongProductsH PRED _⇾_
  spH = record { ε⁻¹∘ε = L.identityˡ ; ε∘ε⁻¹ = L.identityˡ
               ; μ⁻¹∘μ = L.identityˡ ; μ∘μ⁻¹ = L.identityˡ }

  cartH : CartesianH _⇒_ _⇾_
  cartH = record { F-! = refl ; F-▵ = refl ; F-exl = refl ; F-exr = refl }

