-- {-# OPTIONS --safe --without-K #-}
-- Some convenient identity instances.

module Felix.Instances.Identity
   {o ℓ} {obj : Set o} (_⇨_ : obj → obj → Set ℓ)
 where

open import Felix.Object
open import Felix.Raw
open import Felix.Homomorphism

import Felix.Laws as L

module id-instances where

  instance

    Hₒ : Homomorphismₒ obj obj
    Hₒ = id-Hₒ

    H : Homomorphism _⇨_ _⇨_
    H = id-H

    pH : ⦃ _ : Products obj ⦄ ⦃ _ : Category _⇨_ ⦄
       → ProductsH obj _⇨_
    pH = id-ProductsH

    -- bH : ⦃ _ : Products obj ⦄ ⦃ _ : Boolean obj ⦄ ⦃ _ : Category _⇨_ ⦄
    --    → BooleanH obj _⇨_
    -- bH = id-BooleanH

  module _ {q} ⦃ _ : Equivalent q _⇨_ ⦄ ⦃ _ : Category _⇨_ ⦄ where

   instance

    catH : CategoryH _⇨_ _⇨_
    catH = id-CategoryH

    spH : ⦃ _ : Products obj ⦄ ⦃ _ : L.Category _⇨_ ⦄ → StrongProductsH obj _⇨_
    spH = id-StrongProductsH

    cartH : ⦃ _ : Products obj ⦄ ⦃ _ : Cartesian _⇨_ ⦄
            ⦃ _ : L.Category _⇨_ ⦄ ⦃ _ : L.Cartesian _⇨_ ⦄ → CartesianH _⇨_ _⇨_
    cartH = id-CartesianH

    -- sbH : ⦃ _ : Products obj ⦄ ⦃ _ : Boolean obj ⦄ ⦃ _ : L.Category _⇨_ ⦄
    --     → StrongBooleanH obj _⇨_
    -- sbH = id-StrongBooleanH

    -- lH : ⦃ _ : Products obj ⦄ ⦃ _ : Boolean obj ⦄
    --      ⦃ _ : Logic _⇨_ ⦄ ⦃ _ : Cartesian _⇨_ ⦄
    --      ⦃ _ : L.Category _⇨_ ⦄ ⦃ _ : L.Cartesian _⇨_ ⦄ ⦃ _ : L.Logic _⇨_ ⦄
    --    → LogicH _⇨_ _⇨_
    -- lH = id-LogicH
