{-# OPTIONS --safe --without-K #-}
module Felix.Object where

open import Level using (Level)

private variable o : Level ; obj : Set o

record Products (obj : Set o) : Set o where
  infixr 2 _×_
  field
    ⊤ : obj
    _×_ : obj → obj → obj
open Products ⦃ … ⦄ public

record Coproducts (obj : Set o) : Set o where
  infixr 2 _⊎_
  field
    ⊥ : obj
    _⊎_ : obj → obj → obj
open Coproducts ⦃ … ⦄ public

record Exponentials (obj : Set o) : Set o where
  infixr 1 _⇛_
  field
    _⇛_ : obj → obj → obj
open Exponentials ⦃ … ⦄ public
