-- {-# OPTIONS --safe --without-K #-}

open import Level

module Felix.Instances.CAT {o ℓ : Level} where

-- I'd move o & l into Obj, but then I'd have to work with Setω, and Category
-- etc can only handle Set ℓ (for finite ℓ).

open import Data.Product using (_,_)

open import Felix.Object
open import Felix.Raw
open import Felix.Equiv
private module F {ℓ} where open import Felix.Instances.Function ℓ public
open F


record CAT : Set (suc (o ⊔ ℓ)) where
  constructor cat
  field
    {obj} : Set o
    mor : obj → obj → Set ℓ

infix 0 _⤇_
record _⤇_ (𝐴₁ 𝐴₂ : CAT) : Set (o ⊔ ℓ) where
  constructor mk⤇
  open CAT 𝐴₁ renaming (obj to obj₁; mor to _⇨₁_)
  open CAT 𝐴₂ renaming (obj to obj₂; mor to _⇨₂_)
  field
    Fₒ : obj₁ → obj₂
    Fₘ : ∀ {a b : obj₁} → (a ⇨₁ b) → (Fₒ a ⇨₂ Fₒ b)

module CAT-instances where instance

  category : Category _⤇_
  category = record
    { id = mk⤇ id id
    ; _∘_ = λ (mk⤇ Gₒ Gₘ) (mk⤇ Fₒ Fₘ) → mk⤇ (Gₒ ∘ Fₒ) (Gₘ ∘ Fₘ)
    }

  products : Products CAT
  products = record
    { ⊤ = cat {⊤} λ { tt tt → ⊤ }
    ; _×_ = λ (cat {obj₁} _⇨₁_) (cat {obj₂} _⇨₂_) →
        cat {obj₁ × obj₂} λ (a₁ , a₂) (b₁ , b₂) → (a₁ ⇨₁ b₁) × (a₂ ⇨₂ b₂)
    }

  cartesian : Cartesian _⤇_
  cartesian = record
    { ! = mk⤇ ! !
    ; _▵_ = λ (mk⤇ Fₒ Fₘ) (mk⤇ Gₒ Gₘ) → mk⤇ (Fₒ ▵ Gₒ) (Fₘ ▵ Gₘ)
    ; exl = mk⤇ exl exl
    ; exr = mk⤇ exr exr
    }


-- Temporary (I think) bridge to Homomorphism etc

private variable A B : CAT

open import Felix.Homomorphism

open CAT
open _⤇_

toHₒ : (A ⤇ B) → Homomorphismₒ (obj A) (obj B)
toHₒ (mk⤇ Fₒ Fₘ) = record { Fₒ = Fₒ }

toH : (F : A ⤇ B) → Homomorphism (mor A) (mor B) ⦃ Hₒ = toHₒ F ⦄
toH (mk⤇ Fₒ Fₘ) = record { Fₘ = Fₘ }

it-⤇ : ∀
  {obj₁ : Set o} {_⇨₁_ : obj₁ → obj₁ → Set ℓ}
  {obj₂ : Set o} {_⇨₂_ : obj₂ → obj₂ → Set ℓ}
  ⦃ Hₒ : Homomorphismₒ obj₁ obj₂ ⦄ ⦃ H : Homomorphism _⇨₁_ _⇨₂_ ⦄ → 
  cat _⇨₁_ ⤇ cat _⇨₂_
it-⤇ ⦃ Hₒ = Hₒ ⦄ ⦃ H = H ⦄ = mk⤇ (Homomorphismₒ.Fₒ Hₒ) (Homomorphism.Fₘ H)

