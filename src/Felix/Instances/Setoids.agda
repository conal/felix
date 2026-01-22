-- Category of Setoids and Func (congruences)

{-# OPTIONS --safe --without-K #-}

open import Level

module Felix.Instances.Setoids (ℓ : Level) where

-- stdlib
open import Algebra.Core
open import Data.Empty.Polymorphic
open import Data.Product as × using (_,_; <_,_>)
open import Data.Product.Function.NonDependent.Setoid using (<_,_>ₛ; proj₁ₛ; proj₂ₛ)
open import Data.Product.Relation.Binary.Pointwise.NonDependent as P*
open import Data.Sum as ⊎ using ()
open import Data.Sum.Function.Setoid using ([_,_]ₛ; inj₁ₛ; inj₂ₛ)
open import Data.Sum.Relation.Binary.Pointwise as P+ hiding (map)
import Data.Unit as ⊤₀
open import Data.Unit.Polymorphic hiding (tt)
open import Function using (flip; Func; _⟨$⟩_; _∘_; _∘₂_; mk⇔)
import Function.Construct.Identity    as I
import Function.Construct.Composition as C
import Function.Construct.Constant    as K
import Function.Relation.Binary.Setoid.Equality as E
open import Relation.Binary.Bundles using (Setoid)
open import Relation.Binary.Structures using (IsEquivalence)

-- Felix
open import Felix.Raw as Raw using (Products; Coproducts; Exponentials)
open import Felix.Equiv
open import Felix.Laws

open Setoid
open Func

--------------------------------------------------------------------------------
-- Objects/Morphisms in category of Setoids

Zoid = Setoid ℓ ℓ

infix 0 _⟶_
_⟶_ : Zoid → Zoid → Set ℓ
_⟶_ = Func

private
  variable
    A : Zoid

pattern tt = lift ⊤₀.tt

infix 2 _⊨_
pattern _⊨_ t c = record { to = t ; cong = c }

--------------------------------------------------------------------------------
-- Definitions used below

private
  -- Empty Setoid
  𝟘 : Zoid
  𝟘 .Carrier = ⊥
  𝟘 ._≈_ = λ ()
  𝟘 .isEquivalence = record
    { refl = λ { {()} }
    ; sym = λ { {()} }
    ; trans = λ { {()} }
    }

  -- Unit Setoid
  𝟙 : Zoid
  𝟙 .Carrier = ⊤
  𝟙 ._≈_ tt tt = ⊤
  𝟙 .isEquivalence = _

  absurd : Func 𝟘 A
  absurd = (λ ()) ⊨ λ { { () } }

--------------------------------------------------------------------------------
-- Objects

instance

  products : Products Zoid
  products = record { ⊤ = 𝟙 ; _×_ = _×ₛ_ }

  coproducts : Coproducts Zoid
  coproducts = record { ⊥ = 𝟘 ; _⊎_ = _⊎ₛ_ }

  exponentials : Exponentials Zoid
  exponentials = record { _⇛_ = E._⇨_ }

--------------------------------------------------------------------------------
-- Raw

instance

  rawCategory : Raw.Category _⟶_
  rawCategory = record
    { id  = λ {A} → I.function A
    ; _∘_ = flip C.function
    }

  rawCartesian : Raw.Cartesian _⟶_
  rawCartesian = record
    { !   = K.function _ 𝟙 tt
    ; _▵_ = <_,_>ₛ
    ; exl = proj₁ₛ
    ; exr = proj₂ₛ
    }

  rawCocartesian : Raw.Cocartesian _⟶_
  rawCocartesian = record
    { ¡   = absurd
    ; _▿_ = [_,_]ₛ
    ; inl = inj₁ₛ
    ; inr = inj₂ₛ
    }

  rawCartesianClosed : Raw.CartesianClosed _⟶_
  rawCartesianClosed = record
    { curry = λ { {A} {B} {C} (f ⊨ p) →
               (λ a → ×.curry f a ⊨ λ x≈y → p (Setoid.refl A , x≈y))
              ⊨ λ x≈y _ → p (x≈y , Setoid.refl B) }
    ; apply = λ {_} {B} → ×.uncurry _⟨$⟩_ ⊨
       λ { {_} {g , y} (f≈g , x≈y) → Setoid.trans B (f≈g _) (cong g x≈y) }
    }

  rawDistributive : Raw.Distributive _⟶_
  rawDistributive = record
    { distribˡ⁻¹ =
       (λ { (x , ⊎.inj₁ y) → ⊎.inj₁ (x , y) ; (x , ⊎.inj₂ z) → ⊎.inj₂ (x , z) })
      ⊨ λ { (p , inj₁ q) → inj₁ (p , q) ; (p , inj₂ r) → inj₂ (p , r) }
    ; distribʳ⁻¹ =
        (λ { (⊎.inj₁ x , z) → ⊎.inj₁ (x , z) ; (⊎.inj₂ y , z) → ⊎.inj₂ (y , z) })
      ⊨ (λ { (inj₁ x , z) → inj₁ (x , z) ; (inj₂ y , z) → inj₂ (y , z) })
    }

  -- TODO?
  -- rawTraced : Raw.Traced _⟶_
  -- rawTraced = record
  --   { WF = λ {A} {S} {B} f →
  --                 ∀ (x : Carrier A)
  --               → ×.∃₂ λ (y : Carrier B) (z : Carrier S)
  --               → {!   !} -- _≈_ (B * S) (to f (x , z)) (y , z)
  --   -- ∀ (x : a) → ∃₂ λ (y : b) (z : s) → f (x , z) ≡ (y , z)
  --   ; trace = λ {A} {S} {B} f g → (×.proj₁ ∘ g) ⊨ λ { {x} {y} x≈y → {!   !} }
  --   }

--------------------------------------------------------------------------------
-- Equiv

instance

  equivalent : Equivalent ℓ _⟶_
  equivalent = record
    { _≈_   = λ {A} {B} → E._≈_ A B
    ; equiv = λ {A} {B} → E.isEquivalence A B
    }

module ⟶-Reasoning where open ≈-Reasoning public

--------------------------------------------------------------------------------
-- Lawful

instance

  category : Category _⟶_
  category = record
    { identityˡ = λ {_} {B} _ → refl B
    ; identityʳ = λ {_} {B} _ → refl B
    ; assoc     = λ {_} {_} {_} {D} _ → refl D
    ; ∘≈        = λ {_} {_} {C} {_} {_} {_} {k} h≈k f≈g x →
                    trans C (h≈k _) (cong k (f≈g x))
    }

  cartesian : Cartesian _⟶_
  cartesian = record
    { ∀⊤ = λ _ → tt
    ; ∀× = λ {A} {B} {C} {f} {g} {k} → mk⇔
        < cong (Raw.exl {a = B} {b = C}) ∘_ , cong (Raw.exr {a = B} {b = C}) ∘_ >
        (×.uncurry <_,_>)
    ; ▵≈ = <_,_>
    }

  cocartesian : Cocartesian _⟶_
  cocartesian = record
    { ∀⊥ = λ ()
    ; ∀⊎ = λ {A} {B} {C} {f} {g} {k} → mk⇔
        < _∘ ⊎.inj₁ , _∘ ⊎.inj₂ >
        (×.uncurry ⊎.[_,_])
    ; ▿≈ = λ h≈k f≈g → ⊎.[ h≈k , f≈g ]
    }

  cartesianClosed : CartesianClosed _⟶_
  cartesianClosed = record
    { ∀⇛ = λ {_} {_} {C} → mk⇔
      (λ g≈curry-f   → sym C ∘ ×.uncurry g≈curry-f)
      (λ f≈uncurry-g → sym C ∘₂ ×.curry f≈uncurry-g)
    ; curry≈ = ×.curry
    }

  distributive : Distributive _⟶_
  distributive = record
   { distribˡ∘distribˡ⁻¹ = λ where
      {A} {B} {C} (_ , ⊎.inj₁ x) → refl (A ×ₛ (B ⊎ₛ C))
      {A} {B} {C} (_ , ⊎.inj₂ y) → refl (A ×ₛ (B ⊎ₛ C))
    ; distribˡ⁻¹∘distribˡ = λ where
      {A} {B} {C} (⊎.inj₁ _) → refl ((A ×ₛ B) ⊎ₛ (A ×ₛ C))
      {A} {B} {C} (⊎.inj₂ _) → refl ((A ×ₛ B) ⊎ₛ (A ×ₛ C))
    ; distribʳ∘distribʳ⁻¹ = λ where
      {A} {B} {C} (⊎.inj₁ _ , _) → refl ((B ⊎ₛ C) ×ₛ A)
      {A} {B} {C} (⊎.inj₂ _ , _) → refl ((B ⊎ₛ C) ×ₛ A)
    ; distribʳ⁻¹∘distribʳ = λ where
      {A} {B} {C} (⊎.inj₁ _) → refl ((B ×ₛ A) ⊎ₛ (C ×ₛ A))
      {A} {B} {C} (⊎.inj₂ _) → refl ((B ×ₛ A) ⊎ₛ (C ×ₛ A))
    }

  -- Needs laws
  -- traced : Traced _⟶ₛ_
  -- traced = ?
