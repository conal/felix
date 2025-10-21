-- Category of Cardinal numbers by Inverse

{-# OPTIONS --safe --without-K #-}

open import Level

module Felix.Instances.Cardinals (ℓ : Level) where

-- stdlib
open import Data.Product as × using (_,_)
open import Data.Sum as ⊎ using ()
open import Function using (flip ; Func ; Inverse; Injection; _⟨$⟩_)
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
open import Felix.Instances.Setoids ℓ 
             using (Zoid; _⟶_; coproducts; products; exponentials)

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
        ×.× (∀ {b : Carrier B} → _≈_ A (from ≃₁ b) (from ≃₂ b))
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

-- Equivalence of injections
instance
  
  ≼-equivalent : Equivalent ℓ _≼_
  ≼-equivalent = record 
    { _≈_   = λ {A} {B} ≼₁ ≼₂ → Eq._≈_ A B (function ≼₁) (function ≼₂)
    ; equiv = λ {A} {B} →  On.isEquivalence function (Eq.isEquivalence A B) 
    }
    where open Injection

module ≼-Reasoning where open ≈-Reasoning ⦃ ≼-equivalent ⦄ public


open import Felix.Prop

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

--------------------------------------------------------------------------------
-- Example Endofunctors on Card
-- * TODO: find general construction

open import Felix.Object
open import Felix.Homomorphism

open import Data.Sum.Relation.Binary.Pointwise as ⊎ₛ

module _ (X : Cardinal) where instance
  
  -- A + X
  addₒ : Homomorphismₒ Cardinal Cardinal
  addₒ = record { Fₒ = _⊎ X }

  addₘ : Homomorphism _≼_ _≼_
  addₘ = record { Fₘ = λ f → record 
       { to = ⊎.map (to f)  Function.id 
       ; cong = ⊎ₛ.map (cong f) Function.id 
       ; injective = λ { {⊎.inj₁ _} {⊎.inj₁ _} (inj₁ x≈x′) → inj₁ (injective f x≈x′)
                       ; {⊎.inj₂ _} {⊎.inj₂ _} (inj₂ x≈x′) → inj₂ (x≈x′)
                       }
       } 
     }
    where open Injection

  add : CategoryH _≼_ _≼_
  add = record 
    { F-cong = λ { {A} {X} f≈g (⊎.inj₁ x) → inj₁ (f≈g x) ; _ (⊎.inj₂ _) → inj₂ (refl X)}
    ; F-id   = λ { {A} (⊎.inj₁ a) → inj₁ (refl A) ;  (⊎.inj₂ _)  → inj₂ (refl X) }
    ; F-∘    = λ { {A} {_} {C} {f} {g} (⊎.inj₁ _) → inj₁ (refl C)
                 ; {A} {_} {C} {f} {g} (⊎.inj₂ _) → inj₂ (refl X) }
    }
    where open Injection

  -- A * X
  mulₒ : Homomorphismₒ Cardinal Cardinal
  mulₒ = record { Fₒ = _× X }
  
  mulₘ : Homomorphism _≼_ _≼_ ⦃ Hₒ = mulₒ ⦄
  mulₘ = record { Fₘ = λ f → record 
     { to   = ×.map₁ (to f) 
     ; cong = ×.map₁ (cong f) 
     ; injective = ×.map₁ (injective f) 
     } 
    }
    where open Injection

  mul : CategoryH _≼_ _≼_ ⦃ Hₒ = mulₒ ⦄ ⦃ H = mulₘ ⦄
  mul = record 
    { F-cong = λ f≈g (a , _) → f≈g a , refl X 
    ; F-id   = λ {A} _ → refl A , refl X 
    ; F-∘    = λ {_} {_} {C} _ → refl C , refl X 
    }
 
  -- X ^ A
  expₒ : Homomorphismₒ Cardinal Cardinal
  expₒ = record { Fₒ = X ⇛_ }
  
  expₘ : Homomorphism _≼_ _≼_ ⦃ Hₒ = expₒ ⦄
  expₘ  = record { Fₘ = λ {A} {B} f → record 
      { to   = flip C.function (function f) 
      ; cong = λ g≈h x → cong f (g≈h x)
      ; injective = λ eq x → injective f (eq x) 
      } 
    }
    where open Injection

  exp : CategoryH _≼_ _≼_ ⦃ Hₒ = expₒ ⦄ ⦃ H = expₘ ⦄
  exp = record 
    { F-cong = λ f≈g h x → f≈g (h ⟨$⟩ x) 
    ; F-id   = λ {A} _ _ → refl A 
    ; F-∘    = λ {_} {_} {C} _ _ → refl C 
    }

module _ where instance

  succₒ : Homomorphismₒ Cardinal Cardinal
  succₒ = addₒ ⊤

  succₘ : Homomorphism _≼_ _≼_
  succₘ = addₘ ⊤

  succ : CategoryH _≼_ _≼_
  succ = add ⊤
