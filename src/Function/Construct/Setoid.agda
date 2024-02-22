-- agda-categories says that it:
-- was not ported from old function hierarchy, see:
-- https://github.com/agda/agda-stdlib/pull/2240

{-# OPTIONS --without-K --safe #-}

module Function.Construct.Setoid where

  open import Function.Bundles using (Func)
  import Function.Construct.Composition as Comp
  open import Level using (Level)
  open import Relation.Binary.Bundles using (Setoid)


  private
    variable
      a₁ a₂ b₁ b₂ c₁ c₂ : Level

  setoid : Setoid a₁ a₂ → Setoid b₁ b₂ → Setoid _ _
  setoid From To = record
    { Carrier = Func From To
    ; _≈_ = λ f g → ∀ x → Func.to f x To.≈ Func.to g x
    ; isEquivalence = record
      { refl = λ _ → To.refl
      ; sym = λ f≈g x → To.sym (f≈g x)
      ; trans = λ f≈g g≈h x → To.trans (f≈g x) (g≈h x)
      }
    }
    where
      module To = Setoid To
