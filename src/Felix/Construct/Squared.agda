-- {-# OPTIONS --safe --without-K #-}
-- {-# OPTIONS --allow-unsolved-metas #-}

-- Product a category with itself, with a special functor to that category

open import Felix.Object
open import Felix.Raw
open import Felix.Homomorphism
open import Felix.Laws as L
  hiding (Category; Cartesian; CartesianClosed) -- ; Logic

module Felix.Construct.Squared
  {o} {obj : Set o} {ℓ} {_⇨_ : obj → obj → Set ℓ} ⦃ _ : Category _⇨_ ⦄
  ⦃ _ : Products obj ⦄ ⦃ _ : Cartesian _⇨_ ⦄
  {q} ⦃ _ : Equivalent q _⇨_ ⦄ ⦃ _ : L.Category _⇨_ ⦄ ⦃ _ : L.Cartesian _⇨_ ⦄
 where

open import Data.Product using (_,_)


open import Felix.Construct.Product {_⇨₁_ = _⇨_} {_⇨₂_ = _⇨_}
  hiding (module product-homomorphisms) renaming (_⇨_ to _⇨²_) public


private

  -- I'm working on these lemmas in Felix.Reasoning
  postulate
    [exl⊗exl]∘transpose : ∀ {a b c d : obj} →
      (exl ⊗ exl) ∘ transpose {a = a} {b} {c} {d} ≈ exl
    [exr⊗exr]∘transpose : ∀ {a b c d : obj} →
      (exr ⊗ exr) ∘ transpose {a = a} {b} {c} {d} ≈ exr


open import Felix.Instances.CAT

unsquare : cat _⇨²_ ⤇ cat _⇨_
unsquare = mk⤇ (λ (A , B) → A × B) (λ (f , g) → f ⊗ g)

open import Felix.Reasoning

module product-same-homomorphisms where instance

  Hₒ : Homomorphismₒ Obj obj
  Hₒ = toHₒ unsquare
  -- Hₒ = record { Fₒ = λ (A , B) → A × B }

  H : Homomorphism _⇨²_ _⇨_
  H = toH unsquare
  -- H = record { Fₘ = λ (f , g) → f ⊗ g }

  catH : CategoryH _⇨²_ _⇨_
  catH = record { F-id = id⊗id ; F-∘ = sym ⊗∘⊗ }

  pH : ProductsH Obj _⇨_
  pH = record { ε = unitorⁱʳ ; μ = transpose ; ε⁻¹ = unitorᵉʳ ; μ⁻¹ = transpose }

  spH : StrongProductsH Obj _⇨_
  spH = record { ε⁻¹∘ε = unitorᵉʳ∘unitorⁱʳ
               ; ε∘ε⁻¹ = unitorⁱʳ∘unitorᵉʳ
               ; μ⁻¹∘μ = transpose∘transpose
               ; μ∘μ⁻¹ = transpose∘transpose }

  cartH : CartesianH _⇨²_ _⇨_
  cartH = record { F-!   = !⊗!
                 ; F-▵   = sym transpose∘▵⊗▵
                 ; F-exl = [exl⊗exl]∘transpose
                 ; F-exr = [exr⊗exr]∘transpose }
