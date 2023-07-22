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

  infixr 7 _>>_
  _>>_ : (a ⇨ b) → (b ⇨ c) → (a ⇨ c)
  f >> g = g ∘ f

  open import Relation.Binary.PropositionalEquality

  sub : ∀ {i} {I : Set i} {m n : I} (f : I → obj) → m ≡ n → f m ⇨ f n
  sub f refl = id

  sub≡ : a ≡ b → a ⇨ b
  sub≡ = sub id′

open Category ⦃ … ⦄ public

record Monoidal {obj : Set o} ⦃ _ : Products obj ⦄
         (_⇨′_ : obj → obj → Set ℓ)
         ⦃ _ : Category _⇨′_ ⦄
    : Set (o ⊔ ℓ) where
  private infix 0 _⇨_; _⇨_ = _⇨′_
  infixr 7 _⊗_
  field
    unitorᵉˡ : ⊤ × a ⇨ a
    unitorᵉʳ : a × ⊤ ⇨ a
    unitorⁱˡ : a ⇨ ⊤ × a
    unitorⁱʳ : a ⇨ a × ⊤
    assocˡ : a × (b × c) ⇨ (a × b) × c
    assocʳ : (a × b) × c ⇨ a × (b × c)
    _⊗_ : (a ⇨ c) → (b ⇨ d) → (a × b ⇨ c × d)

  first : (a ⇨ c) → (a × b ⇨ c × b)
  first f = f ⊗ id
  second : (a ⇨ c) → (b × a ⇨ b × c)
  second f = id ⊗ f

  twice : (a ⇨ c) → (a × a ⇨ c × c)
  twice f = f ⊗ f

  constˡ : (⊤ ⇨ a) → (b ⇨ a × b)
  constˡ f = first f ∘ unitorⁱˡ

  constʳ : (⊤ ⇨ b) → (a ⇨ a × b)
  constʳ g = second g ∘ unitorⁱʳ
  inAssocˡ′ : ((a × b) × c ⇨ (a′ × b′) × c′) → (a × (b × c) ⇨ a′ × (b′ × c′))
  inAssocˡ′ f = assocʳ ∘ f ∘ assocˡ

  inAssocˡ : (a × b ⇨ a′ × b′) → (a × (b × c) ⇨ a′ × (b′ × c))
  inAssocˡ = inAssocˡ′ ∘̇ first

  inAssocʳ′ : (a × (b × c) ⇨ a′ × (b′ × c′)) → ((a × b) × c ⇨ (a′ × b′) × c′)
  inAssocʳ′ f = assocˡ ∘ f ∘ assocʳ

  inAssocʳ : (b × c ⇨ b′ × c′) → ((a × b) × c ⇨ (a × b′) × c′)
  inAssocʳ = inAssocʳ′ ∘̇ second


-- second I ∘ unitor

open Monoidal ⦃ … ⦄ public
record Braided {obj : Set o} ⦃ _ : Products obj ⦄
         (_⇨′_ : obj → obj → Set ℓ)
         ⦃ _ : Category _⇨′_ ⦄
         ⦃ _ : Monoidal _⇨′_  ⦄
    : Set (o ⊔ ℓ) where
  private infix 0 _⇨_; _⇨_ = _⇨′_
  field
    swap : (a × b) ⇨ (b × a)

  transpose : (a × b) × (c × d) ⇨ (a × c) × (b × d)
  transpose = inAssocʳ′ (second (inAssocˡ′ (first swap )))
  inTranspose : ((a × c) × (b × d) ⇨ (a′ × c′) × (b′ × d′))
              → ((a × b) × (c × d) ⇨ (a′ × b′) × (c′ × d′))
  inTranspose f = transpose ∘ f ∘ transpose


  inSwap : (b × a ⇨ b′ × a′) → (a × b ⇨ a′ × b′)
  inSwap f = swap ∘ f ∘ swap


open Braided ⦃ … ⦄ public


record Symmetric {obj : Set o} ⦃ _ : Products obj ⦄
         (_⇨′_ : obj → obj → Set ℓ)
        -- (_M′_ : obj → obj → obj)
         ⦃ _ : Category _⇨′_ ⦄
         ⦃ _ : Monoidal _⇨′_  ⦄
    : Set (o ⊔ ℓ) where
  private infix 0 _⇨_; _⇨_ = _⇨′_
  -- private infixr 7 _M_; _M_ = _M′_
    -- braidbraid : (braid ∘ braid) ⇨  id

open Symmetric ⦃ … ⦄ public




record Cartesian {obj : Set o} ⦃ _ : Products obj ⦄
         (_⇨′_ : obj → obj → Set ℓ)
         ⦃ _ : Category _⇨′_ ⦄
         ⦃ _ : Monoidal _⇨′_ ⦄
         ⦃ _ : Symmetric _⇨′_ ⦄
    : Set (o ⊔ ℓ) where
  private infix 0 _⇨_; _⇨_ = _⇨′_
  field
    dup : a ⇨ a × a
    !   : a ⇨ ⊤

  exl : a × b ⇨ a
  exl =  unitorᵉʳ ∘ (second !)

  exr : a × b ⇨ b
  exr =  unitorᵉˡ ∘ (first !)
  infixr 7 _▵_
  _▵_ : (a ⇨ c) → (a ⇨ d) → (a ⇨ c × d)
  f ▵ g = (f ⊗ g) ∘ dup

  infixr 4 _⦂_
  _⦂_ : (⊤ ⇨ a) → (⊤ ⇨ b) → (⊤ ⇨ a × b)
  a ⦂ b = (a ⊗ b) ∘ unitorⁱˡ

open Cartesian ⦃ … ⦄ public


record Cocartesian {obj : Set o} ⦃ _ : Coproducts obj ⦄
         (_⇨′_ : obj → obj → Set ℓ)
         ⦃ _ : Category _⇨′_ ⦄
    : Set (o ⊔ ℓ) where
  private infix 0 _⇨_; _⇨_ = _⇨′_
  infixr 7 _▿_
  field
    ¡   : ⊥ ⇨ a
    _▿_ : ∀ {a b c} → (a ⇨ c) → (b ⇨ c) → (a ⊎ b ⇨ c)
    inl : ∀ {a b} → a ⇨ a ⊎ b
    inr : ∀ {a b} → b ⇨ a ⊎ b

  jam : a ⊎ a ⇨ a
  jam = id ▿ id

open Cocartesian ⦃ … ⦄ public

-- TODO: Factor a bunch of functionality out of Cartesian and some out of Cocartesian in Monoidal.


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
         ⦃ _ : Monoidal _⇨′_ ⦄
         ⦃ _ : Symmetric _⇨′_ ⦄
         ⦃ _ : Cartesian _⇨′_ ⦄
    : Set (o ⊔ ℓ) where
  private infix 0 _⇨_; _⇨_ = _⇨′_
  field
    
    curry : (a × b ⇨ c) → (a ⇨ (b ⇛ c))
    apply : (a ⇛ b) × a ⇨ b

  uncurry : (a ⇨ (b ⇛ c)) → (a × b ⇨ c)
  uncurry f = apply ∘ first f

open CartesianClosed ⦃ … ⦄ public
