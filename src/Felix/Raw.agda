{-# OPTIONS --safe --without-K #-}

module Felix.Raw where

open import Level using (Level; _⊔_; suc)
open import Function using (const) renaming (id to id′; _∘_ to _∘̇_)

open import Felix.Object public

private
  variable
    o ℓ o₁ ℓ₁ o₂ ℓ₂ : Level
    obj obj₁ obj₂ : Set o
    a b c d e s : obj
    a′ b′ c′ d′ e′ : obj

record Category {obj : Set o} (_⇨_ : obj → obj → Set ℓ) : Set (o ⊔ ℓ) where
  infixr 9 _∘_
  field
    id  : a ⇨ a
    _∘_ : {a b c : obj} → (g : b ⇨ c) (f : a ⇨ b) → (a ⇨ c)

  open import Relation.Binary.PropositionalEquality

  sub : ∀ {i} {I : Set i} {m n : I} (f : I → obj) → m ≡ n → f m ⇨ f n
  sub f refl = id

  sub≡ : a ≡ b → a ⇨ b
  sub≡ = sub id′

open Category ⦃ … ⦄ public


record Cartesian {obj : Set o} ⦃ _ : Products obj ⦄
         (_⇨′_ : obj → obj → Set ℓ)
         ⦃ _ : Category _⇨′_ ⦄
    : Set (o ⊔ ℓ) where
  private infix 0 _⇨_; _⇨_ = _⇨′_
  infixr 7 _▵_
  field
    !   : a ⇨ ⊤
    _▵_ : (a ⇨ c) → (a ⇨ d) → (a ⇨ c × d)
    exl : a × b ⇨ a
    exr : a × b ⇨ b

  dup : a ⇨ a × a
  dup = id ▵ id

  -- The following operations will probably move to Monoidal or Braided

  infixr 7 _⊗_
  _⊗_ : (a ⇨ c) → (b ⇨ d) → (a × b ⇨ c × d)
  f ⊗ g = f ∘ exl ▵ g ∘ exr

  first : (a ⇨ c) → (a × b ⇨ c × b)
  first f = f ⊗ id

  second : (b ⇨ d) → (a × b ⇨ a × d)
  second g = id ⊗ g

  twice : (a ⇨ c) → (a × a ⇨ c × c)
  twice f = f ⊗ f

  unitorᵉˡ : ⊤ × a ⇨ a
  unitorᵉˡ = exr

  unitorᵉʳ : a × ⊤ ⇨ a
  unitorᵉʳ = exl

  unitorⁱˡ : a ⇨ ⊤ × a
  unitorⁱˡ = ! ▵ id

  unitorⁱʳ : a ⇨ a × ⊤
  unitorⁱʳ = id ▵ !

  constˡ : (⊤ ⇨ a) → (b ⇨ a × b)
  constˡ f = first f ∘ unitorⁱˡ

  constʳ : (⊤ ⇨ b) → (a ⇨ a × b)
  constʳ g = second g ∘ unitorⁱʳ

  assocˡ : a × (b × c) ⇨ (a × b) × c
  assocˡ = second exl ▵ exr ∘ exr

  assocʳ : (a × b) × c ⇨ a × (b × c)
  assocʳ = exl ∘ exl ▵ first exr

  inAssocˡ′ : ((a × b) × c ⇨ (a′ × b′) × c′) → (a × (b × c) ⇨ a′ × (b′ × c′))
  inAssocˡ′ f = assocʳ ∘ f ∘ assocˡ

  inAssocˡ : (a × b ⇨ a′ × b′) → (a × (b × c) ⇨ a′ × (b′ × c))
  inAssocˡ = inAssocˡ′ ∘̇ first

  inAssocʳ′ : (a × (b × c) ⇨ a′ × (b′ × c′)) → ((a × b) × c ⇨ (a′ × b′) × c′)
  inAssocʳ′ f = assocˡ ∘ f ∘ assocʳ

  inAssocʳ : (b × c ⇨ b′ × c′) → ((a × b) × c ⇨ (a × b′) × c′)
  inAssocʳ = inAssocʳ′ ∘̇ second

  swap : a × b ⇨ b × a
  swap = exr ▵ exl

  inSwap : (b × a ⇨ b′ × a′) → (a × b ⇨ a′ × b′)
  inSwap f = swap ∘ f ∘ swap

  transpose : (a × b) × (c × d) ⇨ (a × c) × (b × d)
  transpose = inAssocʳ (inAssocˡ swap)

  inTranspose : ((a × c) × (b × d) ⇨ (a′ × c′) × (b′ × d′))
              → ((a × b) × (c × d) ⇨ (a′ × b′) × (c′ × d′))
  inTranspose f = transpose ∘ f ∘ transpose

  infixr 4 _⦂_
  -- _⦂_ : ⌞ a ⌟ → ⌞ b ⌟ → ⌞ a × b ⌟
  _⦂_ : (⊤ ⇨ a) → (⊤ ⇨ b) → (⊤ ⇨ a × b)
  a ⦂ b = (a ⊗ b) ∘ unitorⁱˡ

open Cartesian ⦃ … ⦄ public


record Traced {obj : Set o} ⦃ _ : Products obj ⦄
         (_⇨′_ : obj → obj → Set ℓ)
         ⦃ _ : Category _⇨′_ ⦄
    : Set (o ⊔ suc ℓ) where
  private infix 0 _⇨_; _⇨_ = _⇨′_
  field
    WF : (a × s ⇨ b × s) → Set ℓ
    trace : (f : a × s ⇨ b × s) → WF f → (a ⇨ b)

open Traced ⦃ … ⦄ public


record CartesianClosed {obj : Set o}
         ⦃ _ : Products obj ⦄ ⦃ _ : Exponentials obj ⦄
         (_⇨′_ : obj → obj → Set ℓ)
         ⦃ _ : Category _⇨′_ ⦄
         ⦃ _ : Cartesian _⇨′_ ⦄
    : Set (o ⊔ ℓ) where
  private infix 0 _⇨_; _⇨_ = _⇨′_
  field
    
    curry : (a × b ⇨ c) → (a ⇨ (b ⇛ c))
    apply : (a ⇛ b) × a ⇨ b

  uncurry : (a ⇨ (b ⇛ c)) → (a × b ⇨ c)
  uncurry f = apply ∘ first f

open CartesianClosed ⦃ … ⦄ public


-- record Logic {obj : Set o} ⦃ products : Products obj ⦄ ⦃ boolean : Boolean obj ⦄
--              (_⇨′_ : obj → obj → Set ℓ) : Set (o ⊔ ℓ) where
--   private infix 0 _⇨_; _⇨_ = _⇨′_
--   field
--     false true : ⊤ ⇨ Bool
--     not : Bool ⇨ Bool
--     ∧ ∨ xor : Bool × Bool ⇨ Bool
--     cond : Bool × (a × a) ⇨ a

-- open Logic ⦃ … ⦄ public
