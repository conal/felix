{-# OPTIONS --safe --without-K #-}
open import Level using (Level; suc; _⊔_)

module Felix.Instances.Pred (m ℓm : Level) where

open import Data.Sum using (inj₁ ; inj₂)
open import Data.Product using (_,_; ∃; proj₁)
open import Function using (_on_)
open import Relation.Binary.PropositionalEquality as ≡ using ()
open import Relation.Binary.Construct.On as On using ()
open import Relation.Unary using (Pred; _⟨×⟩_;  _⟨⊎⟩_ ; _⟨→⟩_; _≐_)
open import Relation.Unary.Polymorphic using (U ; ∅)

open import Felix.Object
open import Felix.Raw as Raw hiding (Category ; Cartesian ; Cocartesian)
open import Felix.Laws using (Category ; Cartesian)
open import Felix.Equiv
private module F {ℓ} where open import Felix.Instances.Function ℓ public
open F

--------------------------------------------------------------------------------
-- Objects

record PRED : Set (suc (m ⊔ ℓm)) where
  constructor mkᵒ
  field
    {ty}  : Set m
    pred  : Pred ty ℓm

instance

  products : Products PRED
  products = record { ⊤ = mkᵒ {⊤} U ; _×_ = λ (mkᵒ P) (mkᵒ Q) → mkᵒ (P ⟨×⟩ Q) }

  coproducts : Coproducts PRED
  coproducts = record { ⊥ = mkᵒ {⊥} ∅ ; _⊎_ = λ (mkᵒ P) (mkᵒ Q) → mkᵒ (P ⟨⊎⟩ Q) }

--------------------------------------------------------------------------------
-- Morphisms

infix 0 _⇒_
record _⇒_ (𝒜 ℬ : PRED) : Set (m ⊔ ℓm) where
  constructor mkᵐ ; open PRED
  field
    {f}  : ty 𝒜 → ty ℬ
    imp  : (pred 𝒜 ⟨→⟩ pred ℬ) f

--------------------------------------------------------------------------------
-- Raw

instance

  rawCategory : Raw.Category _⇒_
  rawCategory = record
    { id   = mkᵐ id
    ; _∘_  = λ (mkᵐ g) (mkᵐ f) → mkᵐ (g ∘ f)
    }

  rawCartesian : Raw.Cartesian _⇒_
  rawCartesian = record
    { !    = mkᵐ !
    ; _▵_  = λ (mkᵐ f) (mkᵐ g) → mkᵐ (f ▵ g)
    ; exl  = mkᵐ exl
    ; exr  = mkᵐ exr
    }

  rawCocartesian : Raw.Cocartesian _⇒_
  rawCocartesian = record
    { ¡ = mkᵐ {f = λ ()} ¡
    ; _▿_ = λ (mkᵐ {f₁} h₁) (mkᵐ {f₂} h₂)
               → mkᵐ {f = f₁ ▿ f₂} λ { {inj₁ _} → h₁ ; {inj₂ _} → h₂ }
    ; inl = λ {P} {Q} → mkᵐ {f = inj₁} id
    ; inr = λ {P} {Q} → mkᵐ {f = inj₂} id
    }

--------------------------------------------------------------------------------
-- Equiv: on the underlying function

instance

  equivalent : Equivalent m _⇒_
  equivalent = record
    { _≈_   = _≈_ on _⇒_.f
    ; equiv = On.isEquivalence _⇒_.f equiv
    }

module ⟶-Reasoning where open ≈-Reasoning public

--------------------------------------------------------------------------------
-- Homomorphisms: Project away the predicates and proofs

instance

  open import Felix.Homomorphism

  Hₒ : Homomorphismₒ PRED (Set m)
  Hₒ = record { Fₒ = PRED.ty }

  H : Homomorphism _⇒_ _⇾_
  H = record { Fₘ = _⇒_.f }

  catH : CategoryH _⇒_ _⇾_
  catH = record
    { F-cong = id
    ; F-id = ⇾-Reasoning.refl≈
    ; F-∘ = ⇾-Reasoning.refl≈
    }

  pH : ProductsH PRED _⇾_
  pH = record { ε = id ; μ = id ; ε⁻¹ = id ; μ⁻¹ = id }

  import Felix.Laws as L

  spH : StrongProductsH PRED _⇾_
  spH = record { ε⁻¹∘ε = L.identityˡ ; ε∘ε⁻¹ = L.identityˡ
               ; μ⁻¹∘μ = L.identityˡ ; μ∘μ⁻¹ = L.identityˡ }

  cartH : CartesianH _⇒_ _⇾_
  cartH = record
    { F-!   = λ _ → ≡.refl
    ; F-▵   = λ _ → ≡.refl
    ; F-exl = λ _ → ≡.refl
    ; F-exr = λ _ → ≡.refl
    }

--------------------------------------------------------------------------------
-- Lawful instances: inherited from function instance

instance

  open import Felix.MakeLawful _⇒_ {ℓ₂ = m} _⇾_

  category : Category _⇒_
  category = LawfulCategoryᶠ

  cartesian : Cartesian _⇒_
  cartesian = LawfulCartesianᶠ
