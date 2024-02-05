{-# OPTIONS --safe --without-K  #-}

module Felix.Instances.Setoid.Raw where

open import Data.Product using (_,_; <_,_>; proj₁; proj₂; uncurry′; ∃₂)
open import Data.Product.Relation.Binary.Pointwise.NonDependent using (_×ₛ_)
open import Data.Sum using ([_,_]; inj₁; inj₂)
open import Data.Sum.Relation.Binary.Pointwise using (inj₁; inj₂)
open import Data.Unit.Polymorphic using (tt) renaming (⊤ to ⊤′)
open import Function using (Congruent; Func; _∘′_; flip′) renaming (_∘_ to _∘ᵈ_)
open import Function.Construct.Composition as Comp
open import Function.Construct.Constant as Const
open import Function.Construct.Identity as Id
open import Function.Construct.Setoid as Fun
open import Level using (_⊔_; suc)
open import Relation.Binary using (Setoid)
open import Relation.Binary.PropositionalEquality as ≡ using ()

open import Felix.Equiv using (Equivalent)
open import Felix.Raw
  using ( Category; _∘_
        ; Cartesian; exl; _⊗_; constʳ
        ; Cocartesian; CartesianClosed; Traced
        ; ⊤; _×_
        )
open import Felix.Instances.Setoid.Type using (module setoid-instances; _⟶_; cong; _⟨$⟩_) public
open setoid-instances public

module setoid-raw-instances where instance

  category : ∀ {c ℓ} → Category {suc (c ⊔ ℓ)} {c ⊔ ℓ} {obj = Setoid c ℓ} _⟶_
  category = record
    { id = Id.function _
    ; _∘_ = flip′ Comp.function
    }

  cartesian : ∀ {c ℓ} → Cartesian {obj = Setoid c ℓ} _⟶_
  cartesian = record
    { ! = Const.function _ ⊤ tt
    ; _▵_ = λ ac ad → record
      { to = < ac ⟨$⟩_ , ad ⟨$⟩_ >
      ; cong = < cong ac , cong ad >
      }
    ; exl = record
      { to = proj₁
      ; cong = proj₁
      }
    ; exr = record
      { to = proj₂
      ; cong = proj₂
      }
    }

  cocartesian : ∀ {c ℓ} → Cocartesian ⦃ coproducts {c} {ℓ} ⦄ _⟶_
  cocartesian {c} {ℓ} = record
    { ¡ = record
      { to = λ { () }
      ; cong = λ { {()} }
      }
    ; _▿_ = λ ac bc → record
      { to = [ ac ⟨$⟩_ , bc ⟨$⟩_ ]
      ; cong = λ where
        (inj₁ x) → cong ac x
        (inj₂ x) → cong bc x
      }
    ; inl = record
      { to = inj₁
      ; cong = inj₁
      }
    ; inr = record
      { to = inj₂
      ; cong = inj₂
      }
    }

  cartesianClosed :
    ∀ {c ℓ} →
    CartesianClosed ⦃ products {c ⊔ ℓ} {c ⊔ ℓ} ⦄ ⦃ exponentials {c} {ℓ} ⦄ _⟶_
  cartesianClosed = record
    { curry = λ {A} {B} f → record
      { to = λ a → record
        { to = λ b → f ⟨$⟩ (a , b)
        ; cong = λ x≈y → cong f (Setoid.refl A , x≈y)
        }
      ; cong = λ x≈y → cong f (x≈y , Setoid.refl B)
      }
    ; apply = λ {A} {B} → record
      { to = uncurry′ _⟨$⟩_
      ; cong = λ { {f , x} {g , y} (f≈g , x≈y) →
        Setoid.trans B (f≈g {x}) (cong g x≈y) }
      }
    }

  equivalent : ∀ {c ℓ} → Equivalent (c ⊔ ℓ) {obj = Setoid c ℓ} _⟶_
  equivalent = record
    { _≈_ = λ {From} {To} f g →
      let open Setoid To
      in ∀ x → f ⟨$⟩ x ≈ g ⟨$⟩ x
    ; equiv = λ {From} {To} →
      let open Setoid To
       in record
         { refl = λ _ → refl
         ; sym = λ f≈g x → sym (f≈g x)
         ; trans = λ f≈g g≈h x → trans (f≈g x) (g≈h x)
         }
    }
