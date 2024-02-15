{-# OPTIONS --safe --without-K #-}
-- Subcategory restricting only morphisms, i.e., complement to full subcategory, which I might rename SubO.

open import Level using (_⊔_)
open import Relation.Unary using (Pred)
open import Data.Product using (∃; _,_; proj₁; proj₂)

open import Felix.Raw
open import Felix.Homomorphism
import Felix.Laws as L

module Felix.Subcategory.Morphism {o ℓ} {obj : Set o}
  (_↠_ : obj → obj → Set ℓ) {m} (M : {a b : obj} → Pred (a ↠ b) m)
  {q} ⦃ _ : Equivalent q _↠_ ⦄ ⦃ _ : Category _↠_ ⦄
 where

private variable a b c d : obj

open import Felix.Prop
open ≈-Reasoning

infix 0 _⇨_
record _⇨_ (a b : obj) : Set (ℓ ⊔ m) where
  constructor mk
  field
    f : a ↠ b
    sat : M f

private
  refl↠ : {f : a ↠ b} → f ≈ f
  refl↠ = refl≈

  sym-identityˡ↠ : ⦃ _ : Products obj ⦄ ⦃ _ : Cartesian _↠_ ⦄
    ⦃ _ : L.Category _↠_ ⦄ ⦃ _ : L.Cartesian _↠_ ⦄ {f : a ↠ b} →
    f ≈ id ∘ f
  sym-identityˡ↠ = sym≈ L.identityˡ

module subcat-instances ⦃ _ : Categoryᴾ M ⦄ where instance

  Hₒ : Homomorphismₒ obj obj
  Hₒ = id-Hₒ

  H : Homomorphism _⇨_ _↠_
  H = record { Fₘ = _⇨_.f }

  eq : Equivalent q _⇨_
  eq = H-equiv

  cat : Category _⇨_
  cat = record
    { id = mk id idᴾ
    ; _∘_ = λ (mk g gᴾ) (mk f fᴾ) → mk (g ∘ f) (gᴾ ∘ᴾ fᴾ)
    }

  catH : CategoryH _⇨_ _↠_
  catH = record { F-cong = λ ~ → ~ ; F-id = refl↠ ; F-∘ = refl↠ }

  module _  ⦃ _ : Products obj ⦄ ⦃ _ : Cartesian _↠_ ⦄ ⦃ _ : Cartesianᴾ M ⦄ where instance

    prodH : ProductsH obj _↠_
    prodH = id-ProductsH

    cart :  Cartesian _⇨_
    cart = record
      { ! = mk ! !ᴾ
      ; _▵_ = λ (mk f fᴾ) (mk g gᴾ) → mk (f ▵ g) (fᴾ ▵ᴾ gᴾ)
      ; exl = mk exl exlᴾ
      ; exr = mk exr exrᴾ
      }

    cartH : ⦃ _ : L.Category _↠_ ⦄ ⦃ _ : L.Cartesian _↠_ ⦄ → CartesianH _⇨_ _↠_
    cartH = record
      { F-! = sym-identityˡ↠
      ; F-▵ = sym-identityˡ↠
      ; F-exl = L.identityʳ
      ; F-exr = L.identityʳ
      }
