-- Category of Cardinal numbers by Inverse

{-# OPTIONS --safe --without-K #-}

open import Level

module Felix.Instances.CardinalsInv (ℓ : Level) where

-- stdlib
open import Data.Product as × using (_,_; _×_)
open import Function using (flip ; Func ; Inverse; Injection)
import Function.Construct.Identity    as I
import Function.Construct.Composition as C
import Function.Construct.Constant    as K
import Function.Properties.Inverse    as E
import Function.Relation.Binary.Setoid.Equality as Eq
open import Relation.Binary.Bundles using (Setoid)
open import Relation.Binary.Construct.On as On using ()

-- felix
open import Felix.Raw as Raw using ()
open import Felix.Equiv 
open import Felix.Laws
open import Felix.Instances.Setoids ℓ using (Zoid; _⟶_)

open Setoid


--------------------------------------------------------------------------------
-- Objects/Morphisms in category of Cardinals

Cardinal = Zoid

infix 0 _≃_
_≃_ = Inverse {ℓ} {ℓ}

infix 3 _≼_ 
_≼_ = Injection {ℓ} {ℓ}

private

  variable A B : Cardinal

  to-function : ∀ {A} {B} → A ≃ B → A ⟶ B 
  to-function A≃B = record { to = to A≃B ; cong = to-cong A≃B }
    where open Inverse

  from-function : ∀ {A} {B} → A ≃ B → B ⟶ A 
  from-function A≃B = record { to = from A≃B ; cong = from-cong A≃B }
    where open Inverse
--------------------------------------------------------------------------------
-- Raw

instance

  rawCategory : Raw.Category _≃_
  rawCategory = record
    { id  = λ {A} → I.inverse A
    ; _∘_ = flip C.inverse
    }

--------------------------------------------------------------------------------
-- Equivalence of Inverses

instance
  
  -- TODO:
  -- use Eq instead?
  equivalent : Equivalent ℓ _≃_
  equivalent = record 
    { _≈_   =  λ {A} {B} ≃₁ ≃₂ → 
          (∀ {a : Carrier A} → _≈_ B (to ≃₁ a) (to ≃₂ a)) 
        × (∀ {b : Carrier B} → _≈_ A (from ≃₁ b) (from ≃₂ b))
    ; equiv = λ {A} {B} → record
      { refl = refl B , refl A 
      ; sym = λ (x , y) → sym B x , sym A y
      ; trans = λ (x , y) (u , v) → trans B x u , trans A y v 
      }
    }
    where open Inverse

module ≃-Reasoning where open ≈-Reasoning public

--------------------------------------------------------------------------------
-- Lawful

instance

  -- TODO:
  -- Cardinals are also a groupoid (https://ncatlab.org/nlab/show/groupoid),
  -- but we'd need to define a notion of groupoid in Felix.

  Cardinals : Category _≃_
  Cardinals = record 
    { identityˡ = λ {A} {B} → refl B , refl A 
    ; identityʳ = λ {A} {B} → refl B , refl A
    ; assoc     = λ {A} {_} {_} {D} → refl D , refl A 
    ; ∘≈        = λ {A} {B} {C} {A≃₁B} {A≃₂B} {B≃₁C} {B≃₂C} (x , y) (u , v) → 
                     (λ {a} → trans C (x { to A≃₁B a }) (to-cong B≃₂C (u {a}))) 
                    , λ {c} → trans A (from-cong A≃₁B y) (v { from B≃₂C c })
    }
    where open Inverse

--------------------------------------------------------------------------------
-- Card category
-- * Cardinal category, but morphisms are injections

open import Felix.Prop


-- Equivalence of injections
instance
  
  ≼-equivalent : Equivalent ℓ _≼_
  ≼-equivalent = record 
    { _≈_   = λ {A} {B} ≼₁ ≼₂ → Eq._≈_ A B (function ≼₁) (function ≼₂)
    ; equiv = λ {A} {B} →  On.isEquivalence function (Eq.isEquivalence A B) 
    }
    where open Injection

module ≼-Reasoning where open ≈-Reasoning ⦃ ≼-equivalent ⦄ public

instance
  
  -- maybe this is all we'd need?
  Cardᴾ : Categoryᴾ λ {A} {B} _ → A ≼ B -- ignore the isomorphism
  Cardᴾ = record 
    { idᴾ  = λ {A} → I.injection A
    ; _∘ᴾ_ = flip C.injection 
    }
  
  -- or constructed directly...
  rawCard : Raw.Category _≼_
  rawCard = record
    { id  = λ {A} → I.injection A
    ; _∘_ = flip C.injection
    }

  Card : Category _≼_
  Card = record 
    { identityˡ = λ {_} {B} _ → refl B 
    ; identityʳ = λ {_} {B} _ → refl B 
    ; assoc     = λ {_} {_} {_} {D} _ → refl D 
    ; ∘≈        = λ {_} {_} {C} {f} {_} {_} {k} h≈k f≈g a → 
                     trans C (h≈k (to f a)) (cong k (f≈g a)) 
    }
    where open Injection
