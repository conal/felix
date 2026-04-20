-- Product a category with itself, with a special functor to that category
{-# OPTIONS --safe --without-K #-}

open import Felix.Object
open import Felix.Raw
open import Felix.Homomorphism
open import Felix.Laws as L
  hiding (Category; Cartesian; CartesianClosed) -- ; Logic

module Felix.Construct.Squared
  {o} {obj : Set o} {ℓ} {_⇨_ : obj → obj → Set ℓ} ⦃ _ : Category _⇨_ ⦄
  ⦃ _ : Products obj ⦄ ⦃ _ : Cartesian _⇨_ ⦄
  {q} ⦃ eq : Equivalent q _⇨_ ⦄ ⦃ _ : L.Category _⇨_ ⦄ ⦃ _ : L.Cartesian _⇨_ ⦄
 where

open import Data.Product using (_,_) renaming (map to _⊗̇_; uncurry to uncurry′)

open import Felix.Construct.Product {_⇨₁_ = _⇨_} {_⇨₂_ = _⇨_}
  hiding (module product-homomorphisms) renaming (_⇨_ to _⇨²_) public

open import Felix.Instances.CAT

unsquare : cat _⇨²_ ⤇ cat _⇨_
unsquare = mk⤇ (λ (A , B) → A × B) (λ (f , g) → f ⊗ g)

open import Felix.Reasoning

module product-same-homomorphisms where
  open ≈-Reasoning ⦃ eq ⦄

  instance
    Hₒ : Homomorphismₒ Obj obj
    Hₒ = toHₒ unsquare
    -- Hₒ = record { Fₒ = λ (A , B) → A × B }

    H : Homomorphism _⇨²_ _⇨_
    H = toH unsquare
    -- H = record { Fₘ = λ (f , g) → f ⊗ g }

    catH : CategoryH _⇨²_ _⇨_
    catH = record { F-cong = uncurry′ ⊗≈ ; F-id = id⊗id ; F-∘ = sym≈ ⊗∘⊗ }

    pH : ProductsH Obj _⇨_
    pH = record { ε = unitorⁱʳ ; μ = transpose ; ε⁻¹ = unitorᵉʳ ; μ⁻¹ = transpose }

    spH : StrongProductsH Obj _⇨_
    spH = record { ε⁻¹∘ε = unitorᵉʳ∘unitorⁱʳ
                 ; ε∘ε⁻¹ = unitorⁱʳ∘unitorᵉʳ
                 ; μ⁻¹∘μ = transpose∘transpose
                 ; μ∘μ⁻¹ = transpose∘transpose }

    cartH : CartesianH _⇨²_ _⇨_
    cartH = record { F-!   = !⊗!
                   ; F-▵   = sym≈ transpose∘▵⊗▵
                   ; F-exl = [exl⊗exl]∘transpose
                   ; F-exr = [exr⊗exr]∘transpose }

  -- Plain (non-instance) definition: competing `product-instances.equivalent`
  -- has the same type, so declaring both as instances makes Agda 2.8 reject
  -- any lookup as ambiguous. Reachable as `product-same-homomorphisms.equivalent`.
  equivalent : Equivalent q _⇨²_
  equivalent = H-equiv

  open import Felix.MakeLawful _⇨²_ _⇨_ ⦃ product-instances.equivalent ⦄ ⦃ eq ⦄

  instance
    catL : L.Category _⇨²_ ⦃ equiv = equivalent ⦄
    catL = LawfulCategoryᶠ
