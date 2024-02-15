{-# OPTIONS --safe --without-K #-}

module Felix.Laws where

open import Level
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Function using (_⇔_; module Equivalence)

open import Felix.Raw as R hiding (Category; Cartesian; CartesianClosed)
open import Felix.Equiv

open Equivalence
open ≈-Reasoning

private
  variable
    o ℓ : Level
    obj : Set o
    a b c d e : obj
    a′ b′ c′ d′ e′ : obj

record Category {obj : Set o} (_⇨′_ : obj → obj → Set ℓ)
                {q} ⦃ equiv : Equivalent q _⇨′_ ⦄
                ⦃ rcat : R.Category _⇨′_ ⦄
       : Set (o ⊔ ℓ ⊔ q) where
  private infix 0 _⇨_; _⇨_ = _⇨′_
  field
    identityˡ : {f : a ⇨ b} → id ∘ f ≈ f
    identityʳ : {f : a ⇨ b} → f ∘ id ≈ f
    assoc     : {f : a ⇨ b} {g : b ⇨ c} {h : c ⇨ d} → (h ∘ g) ∘ f ≈ h ∘ (g ∘ f)

    -- TODO: infix?
    ∘≈ : ∀ {f g : a ⇨ b} {h k : b ⇨ c} → h ≈ k → f ≈ g → h ∘ f ≈ k ∘ g

  -- TODO: replace the assoc field after I've inspected all uses
  ∘-assocʳ : {f : a ⇨ b} {g : b ⇨ c} {h : c ⇨ d} → (h ∘ g) ∘ f ≈ h ∘ (g ∘ f)
  ∘-assocʳ = assoc

  ∘-assocˡ : {f : a ⇨ b} {g : b ⇨ c} {h : c ⇨ d} → h ∘ (g ∘ f) ≈ (h ∘ g) ∘ f
  ∘-assocˡ = sym ∘-assocʳ

  ∘≈ˡ : ∀ {f : a ⇨ b} {h k : b ⇨ c} → h ≈ k → h ∘ f ≈ k ∘ f
  ∘≈ˡ h≈k = ∘≈ h≈k refl

  ∘≈ʳ : ∀ {f g : a ⇨ b} {h : b ⇨ c} → f ≈ g → h ∘ f ≈ h ∘ g
  ∘≈ʳ f≈g = ∘≈ refl f≈g

open Category ⦃ … ⦄ public


open import Data.Product using (_,_) renaming (_×_ to _×ₚ_)

record Cartesian {obj : Set o} ⦃ _ : Products obj ⦄
                 (_⇨′_ : obj → obj → Set ℓ)
                 {q} ⦃ equiv : Equivalent q _⇨′_ ⦄
                 ⦃ _ : R.Category _⇨′_ ⦄ ⦃ _ : R.Cartesian _⇨′_ ⦄
                 ⦃ lCat : Category _⇨′_ ⦄
       : Set (o ⊔ ℓ ⊔ q) where
  private infix 0 _⇨_; _⇨_ = _⇨′_
  field
    ∀⊤ : {f : a ⇨ ⊤} → f ≈ !

    ∀× : {f : a ⇨ b} {g : a ⇨ c} {k : a ⇨ b × c}
       → k ≈ f ▵ g ⇔ (exl ∘ k ≈ f  ×ₚ  exr ∘ k ≈ g)

    -- TODO: infix?
    ▵≈ : {f g : a ⇨ c} {h k : a ⇨ d} → h ≈ k → f ≈ g → h ▵ f ≈ k ▵ g

  ∀×→ : {f : a ⇨ b} {g : a ⇨ c} {k : a ⇨ b × c}
     → k ≈ f ▵ g → (exl ∘ k ≈ f  ×ₚ  exr ∘ k ≈ g)
  ∀×→ = to ∀×

  ∀×← : {f : a ⇨ b} {g : a ⇨ c} {k : a ⇨ b × c}
     → (exl ∘ k ≈ f  ×ₚ  exr ∘ k ≈ g) → k ≈ f ▵ g
  ∀×← = from ∀×

  ▵≈ˡ : {f : a ⇨ c} {h k : a ⇨ d} → h ≈ k → h ▵ f ≈ k ▵ f
  ▵≈ˡ h≈k = ▵≈ h≈k refl

  ▵≈ʳ : {f g : a ⇨ c} {h : a ⇨ d} → f ≈ g → h ▵ f ≈ h ▵ g
  ▵≈ʳ f≈g = ▵≈ refl f≈g

  open import Data.Product using (proj₁; proj₂)
  -- TODO: Generalize Function category from level 0, and use exl & exr in place
  -- of proj₁ & proj₂

  exl∘▵ : {f : a ⇨ b} {g : a ⇨ c} → exl ∘ (f ▵ g) ≈ f
  exl∘▵ = proj₁ (∀×→ refl)

  exr∘▵ : {f : a ⇨ b} {g : a ⇨ c} → exr ∘ (f ▵ g) ≈ g
  exr∘▵ = proj₂ (∀×→ refl)

  -- Specializing:
  exl∘⊗ : {f : a ⇨ c} {g : b ⇨ d} → exl ∘ (f ⊗ g) ≈ f ∘ exl
  exl∘⊗ = exl∘▵
  exr∘⊗ : {f : a ⇨ c} {g : b ⇨ d} → exr ∘ (f ⊗ g) ≈ g ∘ exr
  exr∘⊗ = exr∘▵

  exl∘first : {b : obj} {f : a ⇨ c} → exl ∘ first {b = b} f ≈ f ∘ exl
  exl∘first = exl∘⊗

  exr∘first : {b : obj} {f : a ⇨ c} → exr ∘ first {b = b} f ≈ exr
  exr∘first = exr∘⊗ ; identityˡ

  exl∘second : {a : obj} {g : b ⇨ d} → exl ∘ second {a = a} g ≈ exl
  exl∘second = exl∘⊗ ; identityˡ

  exr∘second : {a : obj} {g : b ⇨ d} → exr ∘ second {a = a} g ≈ g ∘ exr
  exr∘second = exr∘⊗

  exl▵exr : {a b : obj} → exl ▵ exr ≈ id {a = a × b}
  exl▵exr = sym (∀×← (identityʳ , identityʳ))

  ⊗≈ : {a b c d : obj} {f g : a ⇨ c} {h k : b ⇨ d}
     → f ≈ g → h ≈ k → f ⊗ h ≈ g ⊗ k
  ⊗≈ f≈g h≈k = ▵≈ (∘≈ˡ f≈g) (∘≈ˡ h≈k)

  -- ⊗≈ {f = f}{g}{h}{k} f≈g h≈k =
  --   begin
  --     f ⊗ h
  --   ≡⟨⟩
  --     f ∘ exl ▵ h ∘ exr
  --   ≈⟨ ▵≈ (∘≈ˡ f≈g) (∘≈ˡ h≈k) ⟩
  --     g ∘ exl ▵ k ∘ exr
  --   ≡⟨⟩
  --     g ⊗ k
  --   ∎

  ⊗≈ˡ : {a b c d : obj}{f g : a ⇨ c}{h : b ⇨ d}
     → f ≈ g → f ⊗ h ≈ g ⊗ h
  ⊗≈ˡ f≈g = ⊗≈ f≈g refl

  ⊗≈ʳ : {a b c d : obj}{f : a ⇨ c}{h k : b ⇨ d}
     → h ≈ k → f ⊗ h ≈ f ⊗ k
  ⊗≈ʳ h≈k = ⊗≈ refl h≈k

  id⊗id : {a b : obj} → id ⊗ id ≈ id {a = a × b}
  id⊗id = exl▵exr • ▵≈ identityˡ identityˡ

  ▵∘ : {f : a ⇨ b} {g : b ⇨ c} {h : b ⇨ d} → (g ▵ h) ∘ f ≈ g ∘ f ▵ h ∘ f
  ▵∘ {f = f}{g}{h}= ∀×← (∘≈ˡ exl∘▵ • sym assoc , ∘≈ˡ exr∘▵ • sym assoc)

  ⊗∘▵ : {f : a ⇨ b} {g : a ⇨ c} {h : b ⇨ d} {k : c ⇨ e}
      → (h ⊗ k) ∘ (f ▵ g) ≈ h ∘ f ▵ k ∘ g
  ⊗∘▵ {f = f}{g}{h}{k} =
    begin
      (h ⊗ k) ∘ (f ▵ g)
    ≡⟨⟩
      (h ∘ exl ▵ k ∘ exr) ∘ (f ▵ g)
    ≈⟨ ▵∘ ⟩
      (h ∘ exl) ∘ (f ▵ g) ▵ (k ∘ exr) ∘ (f ▵ g)
    ≈⟨ ▵≈ assoc assoc ⟩
      h ∘ exl ∘ (f ▵ g) ▵ k ∘ exr ∘ (f ▵ g)
    ≈⟨ ▵≈ (∘≈ʳ exl∘▵) (∘≈ʳ exr∘▵) ⟩
      h ∘ f ▵ k ∘ g
    ∎

  first∘▵ : {f : a ⇨ b} {g : a ⇨ c} {h : b ⇨ d}
      → first h ∘ (f ▵ g) ≈ h ∘ f ▵ g
  first∘▵ = ⊗∘▵ ; ▵≈ʳ identityˡ

  second∘▵ : {f : a ⇨ b} {g : a ⇨ c} {k : c ⇨ e}
      → second k ∘ (f ▵ g) ≈ f ▵ k ∘ g
  second∘▵ = ⊗∘▵ ; ▵≈ˡ identityˡ

  ⊗∘⊗ : {f : a ⇨ c} {g : b ⇨ d} {h : c ⇨ c′} {k : d ⇨ d′}
      → (h ⊗ k) ∘ (f ⊗ g) ≈ h ∘ f ⊗ k ∘ g
  ⊗∘⊗ = ⊗∘▵ ; ▵≈ ∘-assocˡ ∘-assocˡ

  first∘⊗ : {f : a ⇨ c} {g : b ⇨ d} {h : c ⇨ c′}
      → first h ∘ (f ⊗ g) ≈ h ∘ f ⊗ g
  first∘⊗ = ⊗∘⊗ ; ⊗≈ʳ identityˡ
       -- = first∘▵ ; ▵≈ˡ ∘-assocˡ

  ⊗∘first : {f : a ⇨ c} {h : c ⇨ c′} {k : d ⇨ d′}
      → (h ⊗ k) ∘ first f ≈ h ∘ f ⊗ k
  ⊗∘first = ⊗∘⊗ ; ⊗≈ʳ identityʳ

  ⊗∘second : {g : b ⇨ d} {h : c ⇨ c′} {k : d ⇨ d′}
      → (h ⊗ k) ∘ second g ≈ h ⊗ k ∘ g
  ⊗∘second = ⊗∘⊗ ; ⊗≈ˡ identityʳ

  second∘⊗ : {f : a ⇨ c} {g : b ⇨ d} {k : d ⇨ d′}
      → second k ∘ (f ⊗ g) ≈ f ⊗ k ∘ g
  second∘⊗ = ⊗∘⊗ ; ⊗≈ˡ identityˡ

  first∘first : {b : obj} {f : a ⇨ c} {h : c ⇨ c′}
      → first h ∘ first f ≈ first (h ∘ f)
  first∘first {b = b} = first∘⊗ {b = b}   -- = ⊗∘first

  second∘second : {c : obj} {g : b ⇨ d} {k : d ⇨ d′}
      → second k ∘ second g ≈ second (k ∘ g)
  second∘second {c = c} = second∘⊗ {c = c}   -- = ⊗∘second

  first∘second : {f : a ⇨ c} {g : b ⇨ d}
      → first f ∘ second g ≈ f ⊗ g
  first∘second = first∘⊗ ; ⊗≈ˡ identityʳ

  second∘first : {f : a ⇨ c} {g : b ⇨ d}
      → second g ∘ first f ≈ f ⊗ g
  second∘first = second∘⊗ ; ⊗≈ʳ identityʳ

  -- TODO: redefine first f and second g via ▵ to avoid id ∘ exr and id ∘ exl.
  -- There many be broad consequences.

  unitorᵉˡ∘unitorⁱˡ : ∀ {a : obj} → unitorᵉˡ ∘ unitorⁱˡ {a = a} ≈ id
  unitorᵉˡ∘unitorⁱˡ = exr∘▵

  unitorᵉʳ∘unitorⁱʳ : ∀ {a : obj} → unitorᵉʳ ∘ unitorⁱʳ {a = a} ≈ id
  unitorᵉʳ∘unitorⁱʳ = exl∘▵

  unitorⁱˡ∘unitorᵉˡ : ∀ {a : obj} → unitorⁱˡ ∘ unitorᵉˡ {a = a} ≈ id
  unitorⁱˡ∘unitorᵉˡ = ▵∘ ; ▵≈ ∀⊤ identityˡ ; ▵≈ˡ (sym ∀⊤) ; exl▵exr

  --   (! ▵ id) ∘ exr
  -- ≈ ! ∘ exr ▵ id ∘ exr
  -- ≈ ! ▵ exr
  -- ≈ exl ▵ exr
  -- ≈ id

  unitorⁱʳ∘unitorᵉʳ : ∀ {a : obj} → unitorⁱʳ ∘ unitorᵉʳ {a = a} ≈ id
  unitorⁱʳ∘unitorᵉʳ = ▵∘ ; ▵≈ identityˡ ∀⊤ ; ▵≈ʳ (sym ∀⊤) ; exl▵exr

  --   (id ▵ !) ∘ exl
  -- ≈ id ∘ exl ▵ ! ∘ exl
  -- ≈ exl ▵ !
  -- ≈ exl ▵ exr
  -- ≈ id

  -- swap : a × b ⇨ b × a
  -- swap = exr ▵ exl

  exl∘swap : ∀ {a b : obj} → exl ∘ swap {a = a} {b} ≈ exr
  exl∘swap = exl∘▵

  exr∘swap : ∀ {a b : obj} → exr ∘ swap {a = a} {b} ≈ exl
  exr∘swap = exr∘▵

  swap∘▵ : ∀ {a c d} {f : a ⇨ c} {g : a ⇨ d} → swap ∘ (f ▵ g) ≈ g ▵ f
  swap∘▵ = ▵∘ ; ▵≈ exr∘▵ exl∘▵

  -- swap∘▵ {f = f} {g} =
  --   begin
  --     swap ∘ (f ▵ g)
  --   ≡⟨⟩
  --     (exr ▵ exl) ∘ (f ▵ g)
  --   ≈⟨ ▵∘ ⟩
  --     exr ∘ (f ▵ g) ▵ exl ∘ (f ▵ g)
  --   ≈⟨ ▵≈ exr∘▵ exl∘▵ ⟩
  --     g ▵ f
  --   ∎

  -- TODO: Revisit swap∘swap given swap∘▵

  swap∘swap : ∀ {a b : obj} → swap ∘ swap ≈ id {a = a × b}
  swap∘swap = swap∘▵ ; exl▵exr

  -- swap∘swap =
  --   begin
  --     swap ∘ swap
  --   ≡⟨⟩
  --     swap ∘ (exr ▵ exl)
  --   ≈⟨ swap∘▵ ⟩
  --     exl ▵ exr
  --   ≈⟨ exl▵exr ⟩
  --     id
  --   ∎

open Cartesian ⦃ … ⦄ public


record CartesianClosed {obj : Set o} ⦃ _ : Products obj ⦄
                       ⦃ _ : Exponentials obj ⦄ (_⇨′_ : obj → obj → Set ℓ)
                       {q} ⦃ _ : Equivalent q _⇨′_ ⦄
                       ⦃ _ : R.Category _⇨′_ ⦄
                       ⦃ _ : R.Cartesian _⇨′_ ⦄
                       ⦃ _ : R.CartesianClosed _⇨′_ ⦄
                       ⦃ lCat : Category _⇨′_ ⦄ ⦃ lCart : Cartesian _⇨′_ ⦄
       : Set (o ⊔ ℓ ⊔ q) where
  private infix 0 _⇨_; _⇨_ = _⇨′_
  field
    ∀⇛ : {f : a × b ⇨ c} {g : a ⇨ (b ⇛ c)} → (g ≈ curry f) ⇔ (f ≈ uncurry g)
    -- Note: uncurry g ≡ apply ∘ first g ≡ apply ∘ (g ⊗ id)
    -- RHS is often written "apply ∘ (g ⊗ id)"

    curry≈ : ∀ {f g : a × b ⇨ c} → f ≈ g → curry f ≈ curry g

  ∀⇛→ : {f : a × b ⇨ c} {g : a ⇨ (b ⇛ c)}
      → g ≈ curry f → f ≈ uncurry g
  ∀⇛→ = to ∀⇛

  ∀⇛← : {f : a × b ⇨ c} {g : a ⇨ (b ⇛ c)}
      → f ≈ uncurry g → g ≈ curry f
  ∀⇛← = from ∀⇛

  curry-apply : {a b : obj} → id { a = a ⇛ b } ≈ curry apply
  curry-apply = ∀⇛← (begin
                       apply
                     ≈˘⟨ identityʳ ⟩
                       apply ∘ id
                     ≈˘⟨ ∘≈ʳ id⊗id ⟩
                       apply ∘ (id ⊗ id)
                     ≡⟨⟩
                       apply ∘ first id
                     ≡⟨⟩
                       uncurry id
                     ∎)
