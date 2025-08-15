{-# OPTIONS --safe --without-K #-}

open import Level

module Felix.Instances.Function.Type (ℓ : Level) where

import Data.Empty.Polymorphic as ⊥
import Data.Sum as ⊎
import Data.Unit as ⊤₀
import Data.Unit.Polymorphic as ⊤
open import Data.Product using (_,_) renaming (_×_ to _×̇_)

infixr 0 _⇾_
_⇾_ : Set ℓ → Set ℓ → Set ℓ
A ⇾ B = A → B

pattern tt = lift ⊤₀.tt

module →-instances where

  open import Felix.Object

  instance

    products : Products (Set ℓ)
    products = record { ⊤ = ⊤.⊤ ; _×_ = _×̇_ }

    coproducts : Coproducts (Set ℓ)
    coproducts = record { ⊥ = ⊥.⊥ ; _⊎_ = ⊎._⊎_ }

    exponentials : Exponentials (Set ℓ)
    exponentials = record { _⇛_ = _⇾_ }
