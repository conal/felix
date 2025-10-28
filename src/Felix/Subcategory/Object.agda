-- Subcategory by mapping objects (similar to a full subcategory)
{-# OPTIONS --safe --without-K #-}

-- Note that the J → obj homomorphism needn't be injective. Alternatively, we
-- might take an object predicate (obj → Pred _), which is a more natural
-- translation of the classic notion of subcategory from set theory to type
-- theory. Usage seems more convenient for the formulation in this module, but
-- it may be worth studying more uses. Both styles can be defined via the other,
-- thanks to the power of dependent types.

open import Level using (Level)

open import Felix.Raw
open import Felix.Homomorphism
import Felix.Laws as L
open import Felix.Reasoning

module Felix.Subcategory.Object
  {j} (J : Set j)
  {o ℓ} {obj : Set o}
  (_↠_ : obj → obj → Set ℓ) (let infix 0 _↠_; _↠_ = _↠_)
  ⦃ cat : Category _↠_ ⦄
  {q : Level} ⦃ _ : Equivalent q _↠_ ⦄
  ⦃ Hₒ : Homomorphismₒ J obj ⦄
 where

infix 0 _⇨_
record _⇨_ (a b : J) : Set ℓ where
  constructor mk
  field
    un : Fₒ a ↠ Fₒ b
open _⇨_ public

private
  refl≈↠ : ∀ {a b}{f : a ↠ b} → f ≈ f
  refl≈↠ = refl≈ where open ≈-Reasoning

module sub-object-instances where instance

  category : Category _⇨_
  category = record { id = mk id ; _∘_ = λ (mk g) (mk f) → mk (g ∘ f) }

  cartesian : ⦃ _ : Products obj ⦄ ⦃ _ : Cartesian _↠_ ⦄
              ⦃ _ : Products J ⦄ ⦃ _ : ProductsH J _↠_ ⦄ →
              Cartesian _⇨_
  cartesian = record { !   = mk (ε ∘ !)
                     ; _▵_ = λ (mk f) (mk g) → mk (μ ∘ (f ▵ g))
                     ; exl = mk (exl ∘ μ⁻¹)
                     ; exr = mk (exr ∘ μ⁻¹)
                     }

  cocartesian : ⦃ _ : Coproducts obj ⦄ ⦃ _ : Cocartesian _↠_ ⦄
                ⦃ _ : Coproducts J ⦄ ⦃ _ : CoproductsH J _↠_ ⦄ →
                Cocartesian _⇨_
  cocartesian = record { ¡   = mk (¡ ∘ δ)
                       ; _▿_ = λ (mk f) (mk g) → mk ((f ▿ g) ∘ ν)
                       ; inl = mk (ν⁻¹ ∘ inl)
                       ; inr = mk (ν⁻¹ ∘ inr)
                       }

  traced : ⦃ _ : Products obj ⦄ ⦃ _ : Traced _↠_ ⦄
           ⦃ _ : Products J ⦄ ⦃ _ : ProductsH J _↠_ ⦄ →
           Traced _⇨_
  traced = record
    { WF = λ (mk f) → WF (μ⁻¹ ∘ f ∘ μ)
    ; trace = λ (mk f) wf → mk (trace (μ⁻¹ ∘ f ∘ μ) wf)
    }

  H : Homomorphism _⇨_ _↠_
  H = record { Fₘ = λ (mk f) → f }

  equivalent : Equivalent q _⇨_
  equivalent = H-equiv

  categoryH : CategoryH _⇨_ _↠_
  categoryH = record { F-cong = λ ~ → ~ ; F-id = refl≈↠ ; F-∘ = refl≈↠ }

  productsH : ⦃ _ : Products J ⦄ → ProductsH J _⇨_ ⦃ Hₒ = id-Hₒ ⦄
  productsH = record { ε = id ; μ = id ; ε⁻¹ = id ; μ⁻¹ = id }
  -- TODO: id-ProductsH?

  strongProductsH : ⦃ _ : Products J ⦄ ⦃ _ : L.Category _↠_ ⦄ →
    StrongProductsH J _⇨_ ⦃ Hₒ = id-Hₒ ⦄
  strongProductsH = record
    { ε⁻¹∘ε = L.identityˡ
    ; ε∘ε⁻¹ = L.identityˡ
    ; μ⁻¹∘μ = L.identityˡ
    ; μ∘μ⁻¹ = L.identityˡ
    }
  -- TODO: id-StrongProductsH?

  cartesianH :
    ⦃ _ : Products obj ⦄ ⦃ _ : Cartesian _↠_ ⦄ ⦃ _ : L.Category _↠_ ⦄
    ⦃ _ : Products J ⦄ ⦃ _ : ProductsH J _↠_ ⦄ ⦃ _ : StrongProductsH J _↠_ ⦄
    → CartesianH _⇨_ _↠_
  cartesianH = record { F-! = refl≈↠
                      ; F-▵ = refl≈↠
                      ; F-exl = ∘-assoc-elimʳ μ⁻¹∘μ   -- (exl ∘ μ⁻¹) ∘ μ ≈ exl
                      ; F-exr = ∘-assoc-elimʳ μ⁻¹∘μ   -- (exr ∘ μ⁻¹) ∘ μ ≈ exr
                      }

  open import Felix.MakeLawful _⇨_ _↠_

  l-category : ⦃ _ : L.Category _↠_ ⦄ → L.Category _⇨_
  l-category = LawfulCategoryᶠ

  l-cartesian :
    ⦃ _ : Products obj ⦄ ⦃ _ : Cartesian _↠_ ⦄
    ⦃ _ : Products J ⦄ ⦃ _ : ProductsH J _↠_ ⦄
    ⦃ _ : StrongProductsH J _↠_ ⦄
    ⦃ _ : L.Category _↠_ ⦄ ⦃ _ : L.Cartesian _↠_ ⦄ → L.Cartesian _⇨_
  l-cartesian = LawfulCartesianᶠ
