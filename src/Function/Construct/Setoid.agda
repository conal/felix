-- agda-categories says that it:
-- was not ported from old function hierarchy

{-# OPTIONS --without-K --safe #-}

-- was not ported from old function hierarchy

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
    ; _≈_ = λ f g → ∀ {x} → Func.to f x To.≈ Func.to g x
    ; isEquivalence = record
      { refl = To.refl
      ; sym = λ f≈g → To.sym f≈g
      ; trans = λ f≈g g≈h → To.trans f≈g g≈h
      }
    }
    where
      module To = Setoid To
