-- Compositional morphism properties
{-# OPTIONS --safe --without-K #-}

open import Relation.Unary using (Pred)
open import Felix.Raw

module Felix.Prop {o ℓ} {obj : Set o} {_↠_ : obj → obj → Set ℓ}
 {m} (M : {a b : obj} → Pred (a ↠ b) m) where

open import Level using (_⊔_)

private variable a b c d : obj

record Categoryᴾ ⦃ _ : Category _↠_ ⦄ : Set (o ⊔ m ⊔ ℓ) where
  infixr 9 _∘ᴾ_
  field
    idᴾ : M (id {a = a})
    _∘ᴾ_ : {f : a ↠ b} {g : b ↠ c} → M g → M f → M (g ∘ f)
open Categoryᴾ ⦃ … ⦄ public

record Cartesianᴾ ⦃ _ : Products obj ⦄ ⦃ _ : Category _↠_ ⦄
    ⦃ _ : Cartesian _↠_ ⦄ : Set (o ⊔ m ⊔ ℓ) where
  infixr 7 _▵ᴾ_
  field
    !ᴾ   : M (! {a = a})
    _▵ᴾ_ : {f : a ↠ c} {g : a ↠ d} → M f → M g → M (f ▵ g)
    exlᴾ : M (exl {a = a} {b})
    exrᴾ : M (exr {a = a} {b})
open Cartesianᴾ ⦃ … ⦄ public

-- record Logicᴾ ⦃ _ : Products obj ⦄ ⦃ _ : Boolean obj ⦄ ⦃ _ : Logic _↠_ ⦄
--     : Set (o ⊔ m ⊔ ℓ) where
--   field
--     falseᴾ : M false
--     trueᴾ  : M true
--     notᴾ   : M not
--     ∧ᴾ     : M ∧
--     ∨ᴾ     : M ∨
--     xorᴾ   : M xor
--     condᴾ  : M (cond {a = a})
-- open Logicᴾ ⦃ … ⦄ public
