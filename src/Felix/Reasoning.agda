{-# OPTIONS --safe --without-K #-}

-- Utilities for reasoning about morphism equivalence.
-- Inspired by Categories.Morphism.Reasoning in agda-categories.

open import Felix.Equiv
open import Felix.Raw
open import Felix.Laws as L hiding (Category; Cartesian; CartesianClosed)

module Felix.Reasoning
    {o}{obj : Set o} {ℓ} {_⇨′_ : obj → obj → Set ℓ}
    (let infix 0 _⇨_ ; _⇨_ = _⇨′_)
    ⦃ _ : Category _⇨_ ⦄
    {q} ⦃ _ : Equivalent q _⇨_ ⦄ ⦃ _ : L.Category _⇨_ ⦄
  where

open import Level
open import Function using (_∘′_)

private
  variable
    a b c d e : obj
    a′ b′ c′ d′ e′ : obj
    f g h i j k : a ⇨ b

open import Felix.Equiv
open ≈-Reasoning

module Misc where

  sym≈-sym≈ : {i j : a ⇨ b} {f g : c ⇨ d} → (i ≈ j → f ≈ g) → (j ≈ i → g ≈ f)
  sym≈-sym≈ f≈g = sym≈ ∘′ f≈g ∘′ sym≈
  -- sym≈-sym≈ f≈g i≈j = sym≈ (f≈g (sym≈ i≈j))

  -- I've been able to use sym≈-sym≈, due to implicits

open Misc public


module IntroElim {i : b ⇨ b} (i≈id : i ≈ id) where

  elimˡ  : ∀ {f : a ⇨ b} → i ∘ f ≈ f
  elimˡ  {f = f} = begin
                     i ∘ f
                   ≈⟨ ∘≈ˡ i≈id ⟩
                     id ∘ f
                   ≈⟨ identityˡ ⟩
                     f
                   ∎

  introˡ : ∀ {f : a ⇨ b} → f ≈ i ∘ f
  introˡ = sym≈ elimˡ

  elimʳ  : ∀ {f : b ⇨ c} → f ∘ i ≈ f
  elimʳ  {f = f} = begin
                     f ∘ i
                   ≈⟨ ∘≈ʳ i≈id ⟩
                     f ∘ id
                   ≈⟨ identityʳ ⟩
                     f
                   ∎

  introʳ : ∀ {f : b ⇨ c} → f ≈ f ∘ i
  introʳ = sym≈ elimʳ

  elim-center  : ∀ {f : a ⇨ b} {g : b ⇨ c} → g ∘ i ∘ f ≈ g ∘ f
  elim-center = ∘≈ʳ elimˡ

  intro-center : ∀ {f : a ⇨ b} {g : b ⇨ c} → g ∘ f ≈ g ∘ i ∘ f
  intro-center  = sym≈ elim-center

open IntroElim public


module ∘-Assoc where

  -- TODO: Maybe move ∘-assocˡ′ and ∘-assocʳ′ to Pulls

  ∘-assocˡ′ : ∀ {f : a ⇨ b}{g : b ⇨ c}{h : c ⇨ d}{k : b ⇨ d}
            → h ∘ g ≈ k → h ∘ (g ∘ f) ≈ k ∘ f
  ∘-assocˡ′ h∘g≈k = ∘-assocˡ ; ∘≈ˡ h∘g≈k

  ∘-assocʳ′ : ∀ {f : a ⇨ b}{g : b ⇨ c}{h : a ⇨ c}{k : c ⇨ d}
            → g ∘ f ≈ h → (k ∘ g) ∘ f ≈ k ∘ h
  ∘-assocʳ′ g∘f≈h = ∘-assocʳ ; ∘≈ʳ g∘f≈h


  ∘-assocˡʳ′ : ∀ {f : a ⇨ b}{g : b ⇨ c}{h : c ⇨ d}{i : b ⇨ c′}{j : c′ ⇨ d}
             → h ∘ g ≈ j ∘ i → h ∘ (g ∘ f) ≈ j ∘ (i ∘ f)
  ∘-assocˡʳ′ h∘g≈j∘i = ∘-assocˡ′ h∘g≈j∘i ; ∘-assocʳ

  ∘-assocʳˡ′ : ∀ {f : a ⇨ b}{g : b ⇨ c}{h : c ⇨ d}{i : a ⇨ b′}{j : b′ ⇨ c}
             → g ∘ f ≈ j ∘ i → (h ∘ g) ∘ f ≈ (h ∘ j) ∘ i
  ∘-assocʳˡ′ g∘f≈j∘i = ∘-assocʳ′ g∘f≈j∘i ; ∘-assocˡ


  ∘-assoc-elimˡ : ∀ {f : a ⇨ b}{i : b ⇨ c}{j : c ⇨ b}
                → j ∘ i ≈ id → j ∘ (i ∘ f) ≈ f
  ∘-assoc-elimˡ {f = f}{i}{j} j∘i≈id = ∘-assocˡ ; elimˡ j∘i≈id

  ∘-assoc-elimʳ : ∀ {i : a ⇨ b}{j : b ⇨ a}{f : a ⇨ c}
                → j ∘ i ≈ id → (f ∘ j) ∘ i ≈ f
  ∘-assoc-elimʳ {i = i}{f}{j} j∘i≈id = ∘-assocʳ ; elimʳ j∘i≈id


  ∘-assocʳ³ : {a₀ a₁ a₂ a₃ a₄ : obj}
           {f₁ : a₀ ⇨ a₁}{f₂ : a₁ ⇨ a₂}{f₃ : a₂ ⇨ a₃}{f₄ : a₃ ⇨ a₄}
         → (f₄ ∘ f₃ ∘ f₂) ∘ f₁ ≈ f₄ ∘ f₃ ∘ f₂ ∘ f₁
  ∘-assocʳ³ = ∘≈ʳ ∘-assocʳ • ∘-assocʳ

  ∘-assocʳ⁴ : {a₀ a₁ a₂ a₃ a₄ a₅ : obj}
     {f₁ : a₀ ⇨ a₁}{f₂ : a₁ ⇨ a₂}{f₃ : a₂ ⇨ a₃}{f₄ : a₃ ⇨ a₄}{f₅ : a₄ ⇨ a₅}
   → (f₅ ∘ f₄ ∘ f₃ ∘ f₂) ∘ f₁ ≈ f₅ ∘ f₄ ∘ f₃ ∘ f₂ ∘ f₁
  ∘-assocʳ⁴ = ∘≈ʳ ∘-assocʳ³ • ∘-assocʳ

  ∘-assocʳ⁵ : {a₀ a₁ a₂ a₃ a₄ a₅ a₆ : obj}
     {f₁ : a₀ ⇨ a₁}{f₂ : a₁ ⇨ a₂}{f₃ : a₂ ⇨ a₃}{f₄ : a₃ ⇨ a₄}{f₅ : a₄ ⇨ a₅}{f₆ : a₅ ⇨ a₆}
   → (f₆ ∘ f₅ ∘ f₄ ∘ f₃ ∘ f₂) ∘ f₁ ≈ f₆ ∘ f₅ ∘ f₄ ∘ f₃ ∘ f₂ ∘ f₁
  ∘-assocʳ⁵ = ∘≈ʳ ∘-assocʳ⁴ • ∘-assocʳ

  ∘-assocʳ⁶ : {a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ : obj}
     {f₁ : a₀ ⇨ a₁}{f₂ : a₁ ⇨ a₂}{f₃ : a₂ ⇨ a₃}{f₄ : a₃ ⇨ a₄}{f₅ : a₄ ⇨ a₅}{f₆ : a₅ ⇨ a₆}{f₇ : a₆ ⇨ a₇}
   → (f₇ ∘ f₆ ∘ f₅ ∘ f₄ ∘ f₃ ∘ f₂) ∘ f₁ ≈ f₇ ∘ f₆ ∘ f₅ ∘ f₄ ∘ f₃ ∘ f₂ ∘ f₁
  ∘-assocʳ⁶ = ∘≈ʳ ∘-assocʳ⁵ • ∘-assocʳ

  ∘-assocˡ³ : {a₀ a₁ a₂ a₃ a₄ : obj}
           {f₁ : a₀ ⇨ a₁}{f₂ : a₁ ⇨ a₂}{f₃ : a₂ ⇨ a₃}{f₄ : a₃ ⇨ a₄}
         → f₄ ∘ f₃ ∘ f₂ ∘ f₁ ≈ (f₄ ∘ f₃ ∘ f₂) ∘ f₁
  ∘-assocˡ³ = sym≈ ∘-assocʳ³

  ∘-assocˡ⁴ : {a₀ a₁ a₂ a₃ a₄ a₅ : obj}
     {f₁ : a₀ ⇨ a₁}{f₂ : a₁ ⇨ a₂}{f₃ : a₂ ⇨ a₃}{f₄ : a₃ ⇨ a₄}{f₅ : a₄ ⇨ a₅}
   → f₅ ∘ f₄ ∘ f₃ ∘ f₂ ∘ f₁ ≈ (f₅ ∘ f₄ ∘ f₃ ∘ f₂) ∘ f₁
  ∘-assocˡ⁴ = sym≈ ∘-assocʳ⁴

  ∘-assocˡ⁵ : {a₀ a₁ a₂ a₃ a₄ a₅ a₆ : obj}
     {f₁ : a₀ ⇨ a₁}{f₂ : a₁ ⇨ a₂}{f₃ : a₂ ⇨ a₃}{f₄ : a₃ ⇨ a₄}{f₅ : a₄ ⇨ a₅}
       {f₆ : a₅ ⇨ a₆}
   → f₆ ∘ f₅ ∘ f₄ ∘ f₃ ∘ f₂ ∘ f₁ ≈ (f₆ ∘ f₅ ∘ f₄ ∘ f₃ ∘ f₂) ∘ f₁
  ∘-assocˡ⁵ = sym≈ ∘-assocʳ⁵

  ∘-assocˡ⁶ : {a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ : obj}
     {f₁ : a₀ ⇨ a₁}{f₂ : a₁ ⇨ a₂}{f₃ : a₂ ⇨ a₃}{f₄ : a₃ ⇨ a₄}{f₅ : a₄ ⇨ a₅}
       {f₆ : a₅ ⇨ a₆}{f₇ : a₆ ⇨ a₇}
   → f₇ ∘ f₆ ∘ f₅ ∘ f₄ ∘ f₃ ∘ f₂ ∘ f₁ ≈ (f₇ ∘ f₆ ∘ f₅ ∘ f₄ ∘ f₃ ∘ f₂) ∘ f₁
  ∘-assocˡ⁶ = sym≈ ∘-assocʳ⁶

  ∘≈ʳ² : ∀ {a₀ a₁ a₂ a₃ : obj}{f₁ g₁ : a₀ ⇨ a₁}{f₂ : a₁ ⇨ a₂}{f₃ : a₂ ⇨ a₃}
    → f₁ ≈ g₁ → f₃ ∘ f₂ ∘ f₁ ≈ f₃ ∘ f₂ ∘ g₁
  ∘≈ʳ² = ∘≈ʳ ∘′ ∘≈ʳ

  ∘≈ʳ³ : {a₀ a₁ a₂ a₃ a₄ : obj}
     {f₁ g₁ : a₀ ⇨ a₁}{f₂ : a₁ ⇨ a₂}{f₃ : a₂ ⇨ a₃}{f₄ : a₃ ⇨ a₄}
   → f₁ ≈ g₁ → f₄ ∘ f₃ ∘ f₂ ∘ f₁ ≈ f₄ ∘ f₃ ∘ f₂ ∘ g₁
  ∘≈ʳ³ = ∘≈ʳ² ∘′ ∘≈ʳ

  ∘≈ʳ⁴ : {a₀ a₁ a₂ a₃ a₄ a₅ : obj}
     {f₁ g₁ : a₀ ⇨ a₁}{f₂ : a₁ ⇨ a₂}{f₃ : a₂ ⇨ a₃}{f₄ : a₃ ⇨ a₄}{f₅ : a₄ ⇨ a₅}
   → f₁ ≈ g₁ → f₅ ∘ f₄ ∘ f₃ ∘ f₂ ∘ f₁ ≈ f₅ ∘ f₄ ∘ f₃ ∘ f₂ ∘ g₁
  ∘≈ʳ⁴ = ∘≈ʳ³ ∘′ ∘≈ʳ

  ∘≈ʳ⁵ : {a₀ a₁ a₂ a₃ a₄ a₅ a₆ : obj}
     {f₁ g₁ : a₀ ⇨ a₁}{f₂ : a₁ ⇨ a₂}{f₃ : a₂ ⇨ a₃}{f₄ : a₃ ⇨ a₄}{f₅ : a₄ ⇨ a₅}
       {f₆ : a₅ ⇨ a₆}
   → f₁ ≈ g₁ → f₆ ∘ f₅ ∘ f₄ ∘ f₃ ∘ f₂ ∘ f₁ ≈ f₆ ∘ f₅ ∘ f₄ ∘ f₃ ∘ f₂ ∘ g₁
  ∘≈ʳ⁵ = ∘≈ʳ⁴ ∘′ ∘≈ʳ

  ∘≈ʳ⁶ : {a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ : obj}
     {f₁ g₁ : a₀ ⇨ a₁}{f₂ : a₁ ⇨ a₂}{f₃ : a₂ ⇨ a₃}{f₄ : a₃ ⇨ a₄}{f₅ : a₄ ⇨ a₅}
       {f₆ : a₅ ⇨ a₆}{f₇ : a₆ ⇨ a₇}
   → f₁ ≈ g₁ → f₇ ∘ f₆ ∘ f₅ ∘ f₄ ∘ f₃ ∘ f₂ ∘ f₁ ≈ f₇ ∘ f₆ ∘ f₅ ∘ f₄ ∘ f₃ ∘ f₂ ∘ g₁
  ∘≈ʳ⁶ = ∘≈ʳ⁵ ∘′ ∘≈ʳ

open ∘-Assoc public


-- Stolen nearly intact from agda-categories
module Cancel {i : b ⇨ c} {h : c ⇨ b} (inv : h ∘ i ≈ id) where

  cancelʳ : {f : b ⇨ d} → (f ∘ h) ∘ i ≈ f
  cancelʳ {f = f} =
    begin
      (f ∘ h) ∘ i
    ≈⟨ ∘-assocʳ′ inv ⟩
      f ∘ id
    ≈⟨ identityʳ ⟩
      f
    ∎

  -- insertʳ : {f : b ⇨ d} → f ≈ (f ∘ h) ∘ i
  -- insertʳ = sym≈ cancelʳ

  cancelˡ : {f : a ⇨ b} →  h ∘ (i ∘ f) ≈ f
  cancelˡ {f = f} =
    begin
      h ∘ (i ∘ f)
    ≈⟨ ∘-assocˡ′ inv ⟩
      id ∘ f
    ≈⟨ identityˡ ⟩
      f
    ∎

  -- insertˡ : {f : a ⇨ b} →  f ≈ h ∘ (i ∘ f)
  -- insertˡ = Equiv.sym≈ cancelˡ

  cancelInner : {f : b ⇨ d} {g : a ⇨ b} → (f ∘ h) ∘ (i ∘ g) ≈ f ∘ g
  cancelInner {f = f} {g = g} =
    begin
      (f ∘ h) ∘ (i ∘ g)
    ≈⟨ ∘-assocˡ′ cancelʳ ⟩
      f ∘ g
    ∎

open Cancel public


module Inverses
   ⦃ _ : Products obj ⦄ ⦃ _ : Cartesian _⇨_ ⦄ ⦃ _ : L.Cartesian _⇨_ ⦄ where

  ∘-inverse : ∀ {f : a ⇨ b}{f⁻¹ : b ⇨ a}{g : b ⇨ c}{g⁻¹ : c ⇨ b} →
    f⁻¹ ∘ f ≈ id → g⁻¹ ∘ g ≈ id → (f⁻¹ ∘ g⁻¹) ∘ (g ∘ f) ≈ id
  ∘-inverse f⁻¹∘f≈id g⁻¹∘g≈id = cancelInner g⁻¹∘g≈id ; f⁻¹∘f≈id

  ⊗-inverse : ∀ {f : a ⇨ c}{f⁻¹ : c ⇨ a}{g : b ⇨ d}{g⁻¹ : d ⇨ b} →
     f⁻¹ ∘ f ≈ id → g⁻¹ ∘ g ≈ id → (f⁻¹ ⊗ g⁻¹) ∘ (f ⊗ g) ≈ id
  ⊗-inverse f⁻¹∘f≈id g⁻¹∘g≈id =
    ⊗∘⊗ ; ⊗≈ f⁻¹∘f≈id g⁻¹∘g≈id ; id⊗id

  first-inverse : ∀ {b : obj}{f : a ⇨ c}{f⁻¹ : c ⇨ a} →
     f⁻¹ ∘ f ≈ id → first {b = b} f⁻¹ ∘ first f ≈ id
  first-inverse {b = b} f⁻¹∘f≈id = ⊗-inverse f⁻¹∘f≈id (identityˡ {b = b})

  second-inverse : ∀ {a : obj}{g : b ⇨ d}{g⁻¹ : d ⇨ b} →
    g⁻¹ ∘ g ≈ id → second {a = a} g⁻¹ ∘ second g ≈ id
  second-inverse {a = a} g⁻¹∘g≈id = ⊗-inverse (identityˡ {a = a}) g⁻¹∘g≈id

open Inverses public


module Assoc
  ⦃ _ : Products obj ⦄ ⦃ _ : Cartesian _⇨_ ⦄ ⦃ _ : L.Cartesian _⇨_ ⦄ where

  assocˡ∘assocʳ : assocˡ ∘ assocʳ {a = a}{b}{c} ≈ id
  assocˡ∘assocʳ =
    begin
      assocˡ ∘ assocʳ
    ≡⟨⟩
      (second exl ▵ exr ∘ exr) ∘ (exl ∘ exl ▵ first exr)
    ≈⟨ ▵∘ ⟩
      second exl ∘ (exl ∘ exl ▵ first exr) ▵ (exr ∘ exr) ∘ (exl ∘ exl ▵ first exr)
    -- ≈⟨ ▵≈ second∘▵ ∘-assocʳ ⟩
    --   (exl ∘ exl ▵ exl ∘ first exr) ▵ exr ∘ exr ∘ (exl ∘ exl ▵ first exr)
    -- ≈⟨ ▵≈ (▵≈ʳ exl∘⊗) (∘≈ʳ exr∘▵ ; exr∘first) ⟩
    -- -- The preceding commented group of lines is replaced by the following line.
    -- -- Likewise below. For faster compiles, but maybe not worth it.
    ≈⟨ ▵≈ (second∘▵ ; ▵≈ʳ exl∘⊗) (∘-assocʳ ; ∘≈ʳ exr∘▵ ; exr∘first) ⟩
      (exl ∘ exl ▵ exr ∘ exl) ▵ exr
    -- ≈⟨ ▵≈ˡ (sym≈ ▵∘) ⟩
    --   (exl ▵ exr) ∘ exl ▵ exr
    -- ≈⟨ ▵≈ˡ (∘≈ˡ exl▵exr ; identityˡ) ⟩
    ≈⟨ ▵≈ˡ (sym≈ ▵∘ ; elimˡ exl▵exr) ⟩
      exl ▵ exr
    ≈⟨ exl▵exr ⟩
      id
    ∎

  assocʳ∘assocˡ : assocʳ ∘ assocˡ {a = a}{b}{c} ≈ id
  assocʳ∘assocˡ =
    begin
      assocʳ ∘ assocˡ
    ≡⟨⟩
      (exl ∘ exl ▵ first exr) ∘ (second exl ▵ exr ∘ exr)
    ≈⟨ ▵∘ ⟩
      (exl ∘ exl) ∘ (second exl ▵ exr ∘ exr) ▵ first exr ∘ (second exl ▵ exr ∘ exr)
    -- ≈⟨ ▵≈ ∘-assocʳ first∘▵ ⟩
    --   exl ∘ exl ∘ (second exl ▵ exr ∘ exr) ▵ (exr ∘ second exl ▵ exr ∘ exr)
    -- ≈⟨ ▵≈ (∘≈ʳ exl∘▵) (▵≈ˡ exr∘second) ⟩
    ≈⟨ ▵≈ (∘-assocʳ ; ∘≈ʳ exl∘▵) (first∘▵ ; ▵≈ˡ exr∘second) ⟩
      exl ∘ second exl ▵ (exl ∘ exr ▵ exr ∘ exr)
    ≈⟨ ▵≈ exl∘second (sym≈ ▵∘) ⟩
      exl ▵ (exl ▵ exr) ∘ exr
    ≈⟨ ▵≈ʳ (elimˡ exl▵exr) ⟩
      exl ▵ exr
    ≈⟨ exl▵exr ⟩
      id
    ∎

  assocʳ∘▵ : ∀ {f : a ⇨ a′} {g : a ⇨ b′} {h : a ⇨ c′} →
    assocʳ ∘ ((f ▵ g) ▵ h) ≈ f ▵ (g ▵ h)
  assocʳ∘▵ {f = f} {g} {h} =
    begin
      assocʳ ∘ ((f ▵ g) ▵ h)
    ≡⟨⟩
      (exl ∘ exl ▵ first exr) ∘ ((f ▵ g) ▵ h)
    ≈⟨ ▵∘ ⟩
      (exl ∘ exl) ∘ ((f ▵ g) ▵ h) ▵ first exr ∘ ((f ▵ g) ▵ h)
    ≈⟨ ▵≈ (∘-assocʳ ; ∘≈ʳ exl∘▵) first∘▵ ⟩
      exl ∘ (f ▵ g) ▵ (exr ∘ (f ▵ g) ▵ h)
    ≈⟨ ▵≈ exl∘▵ (▵≈ˡ exr∘▵) ⟩
      f ▵ (g ▵ h)
    ∎

  assocˡ∘▵ : ∀ {f : a ⇨ a′} {g : a ⇨ b′} {h : a ⇨ c′} →
    assocˡ ∘ (f ▵ (g ▵ h)) ≈ (f ▵ g) ▵ h
  assocˡ∘▵ {f = f} {g} {h} =
    begin
      assocˡ ∘ (f ▵ (g ▵ h))
    ≡⟨⟩
      (second exl ▵ exr ∘ exr) ∘ (f ▵ (g ▵ h))
    ≈⟨ ▵∘ ⟩
      second exl ∘ (f ▵ (g ▵ h)) ▵ (exr ∘ exr) ∘ (f ▵ (g ▵ h))
    ≈⟨ ▵≈ second∘▵ (∘-assocʳ ; ∘≈ʳ exr∘▵) ⟩
      (f ▵ exl ∘ (g ▵ h)) ▵ exr ∘ (g ▵ h)
    ≈⟨ ▵≈ (▵≈ʳ exl∘▵) exr∘▵ ⟩
      (f ▵ g) ▵ h
    ∎

  -- TODO: rework ⊗⊗∘assocʳ below, given assocʳ∘▵

  ⊗⊗∘assocʳ : ∀ {f : a ⇨ a′}{g : b ⇨ b′}{h : c ⇨ c′}
           → (f ⊗ (g ⊗ h)) ∘ assocʳ ≈ assocʳ ∘ ((f ⊗ g) ⊗ h)
  ⊗⊗∘assocʳ {f = f}{g}{h} =
    begin
      (f ⊗ (g ⊗ h)) ∘ assocʳ
    ≡⟨⟩
      (f ⊗ (g ⊗ h)) ∘ (exl ∘ exl ▵ first exr)
    ≈⟨ ⊗∘▵ ⟩
      f ∘ exl ∘ exl ▵ (g ⊗ h) ∘ first exr
    -- ≈⟨ ▵≈ʳ ⊗∘first ⟩
    --   f ∘ exl ∘ exl ▵ (g ∘ exr ⊗ h)
    -- ≈⟨ ▵≈ʳ (⊗≈ˡ (sym≈ exr∘⊗)) ⟩
    --   f ∘ exl ∘ exl ▵ (exr ∘ (f ⊗ g) ⊗ h)
    -- ≈⟨ ▵≈ʳ (sym≈ first∘⊗) ⟩
    ≈⟨ ▵≈ʳ (⊗∘first ; ⊗≈ˡ (sym≈ exr∘⊗) ; sym≈ first∘⊗) ⟩
      f ∘ exl ∘ exl ▵ first exr ∘ ((f ⊗ g) ⊗ h)
    -- ≈⟨ ▵≈ˡ (∘-assocˡʳ′ (sym≈ exl∘⊗)) ⟩
    --   exl ∘ (f ⊗ g) ∘ exl ▵ first exr ∘ ((f ⊗ g) ⊗ h)
    -- ≈⟨ ▵≈ˡ (∘≈ʳ (sym≈ exl∘⊗)) ⟩
    --   exl ∘ exl ∘ ((f ⊗ g) ⊗ h) ▵ first exr ∘ ((f ⊗ g) ⊗ h)
    -- ≈⟨ ▵≈ˡ ∘-assocˡ ⟩
    ≈⟨ ▵≈ˡ (∘-assocˡʳ′ (sym≈ exl∘⊗) ; ∘≈ʳ (sym≈ exl∘⊗) ; ∘-assocˡ) ⟩
      (exl ∘ exl) ∘ ((f ⊗ g) ⊗ h) ▵ first exr ∘ ((f ⊗ g) ⊗ h)
    ≈⟨ sym≈ ▵∘ ⟩
      (exl ∘ exl ▵ first exr) ∘ ((f ⊗ g) ⊗ h)
    ≡⟨⟩
      assocʳ ∘ ((f ⊗ g) ⊗ h)
    ∎

  ⊗⊗∘assocˡ : ∀ {f : a ⇨ a′}{g : b ⇨ b′}{h : c ⇨ c′}
           → ((f ⊗ g) ⊗ h) ∘ assocˡ ≈ assocˡ ∘ (f ⊗ (g ⊗ h))
  ⊗⊗∘assocˡ {f = f}{g}{h} =
    begin
      ((f ⊗ g) ⊗ h) ∘ assocˡ
    ≡⟨⟩
      ((f ⊗ g) ⊗ h) ∘ (second exl ▵ exr ∘ exr)
    ≈⟨ ⊗∘▵ ⟩
      (f ⊗ g) ∘ second exl ▵ h ∘ exr ∘ exr
    -- ≈⟨ ▵≈ˡ ⊗∘second ⟩
    --   (f ⊗ g ∘ exl) ▵ h ∘ exr ∘ exr
    -- ≈⟨ ▵≈ˡ (⊗≈ʳ (sym≈ exl∘⊗)) ⟩
    ≈⟨ ▵≈ˡ (⊗∘second ; ⊗≈ʳ (sym≈ exl∘⊗)) ⟩
      (f ⊗ exl ∘ (g ⊗ h)) ▵ h ∘ exr ∘ exr
    -- ≈⟨ ▵≈ʳ (∘-assocˡʳ′ (sym≈ exr∘⊗)) ⟩
    --   (f ⊗ exl ∘ (g ⊗ h)) ▵ exr ∘ (g ⊗ h) ∘ exr
    -- ≈⟨ ▵≈ʳ (∘≈ʳ (sym≈ exr∘⊗)) ⟩
    ≈⟨ ▵≈ʳ (∘-assocˡʳ′ (sym≈ exr∘⊗) ; ∘≈ʳ (sym≈ exr∘⊗)) ⟩
      (f ⊗ exl ∘ (g ⊗ h)) ▵ exr ∘ exr ∘ (f ⊗ (g ⊗ h))
    ≈⟨ ▵≈ (sym≈ second∘⊗) ∘-assocˡ ⟩
      second exl ∘ (f ⊗ (g ⊗ h)) ▵ (exr ∘ exr) ∘ (f ⊗ (g ⊗ h))
    ≈⟨ sym≈ ▵∘ ⟩
      (second exl ▵ exr ∘ exr) ∘ (f ⊗ (g ⊗ h))
    ≡⟨⟩
      assocˡ ∘ (f ⊗ (g ⊗ h))
    ∎

  first-first∘assocˡ : ∀ {b c : obj}{f : a ⇨ d}
    → first {b = c} (first {b = b} f) ∘ assocˡ ≈ assocˡ ∘ first f
  first-first∘assocˡ = ⊗⊗∘assocˡ ; ∘≈ʳ (⊗≈ʳ id⊗id)

  -- first-first∘assocˡ {f = f} =
  --   begin
  --     first (first f) ∘ assocˡ
  --   ≡⟨⟩
  --     ((f ⊗ id) ⊗ id) ∘ assocˡ
  --   ≈⟨ ⊗⊗∘assocˡ ⟩
  --     assocˡ ∘ (f ⊗ (id ⊗ id))
  --   ≈⟨ ∘≈ʳ (⊗≈ʳ id⊗id) ⟩
  --     assocˡ ∘ (f ⊗ id)
  --   ≡⟨⟩
  --     assocˡ ∘ first f
  --   ∎

  first-first : ∀ {b c : obj} {f : a ⇨ d}
    → first {b = c} (first {b = b} f) ≈ assocˡ ∘ first f ∘ assocʳ -- inAssocʳ f
  first-first {f = f} =
    begin
      first (first f)
    ≈⟨ sym≈ (elimʳ assocˡ∘assocʳ) ⟩
      first (first f) ∘ assocˡ ∘ assocʳ
    ≈⟨ ∘-assocˡʳ′ first-first∘assocˡ ⟩
      assocˡ ∘ first f ∘ assocʳ
    ∎

  inAssocˡ′-inverse : ∀
    {f : (a × b) × c ⇨ (a′ × b′) × c′} {f⁻¹ : (a′ × b′) × c′ ⇨ (a × b) × c} →
    f⁻¹ ∘ f ≈ id → inAssocˡ′ f⁻¹ ∘ inAssocˡ′ f ≈ id
  inAssocˡ′-inverse {f = f} {f⁻¹} f⁻¹∘f≈id =
    begin
      inAssocˡ′ f⁻¹ ∘ inAssocˡ′ f
    ≡⟨⟩
      (assocʳ ∘ f⁻¹ ∘ assocˡ) ∘ (assocʳ ∘ f ∘ assocˡ)
    ≈⟨ (∘≈ˡ ∘-assocˡ ; cancelInner assocˡ∘assocʳ) ⟩
      (assocʳ ∘ f⁻¹) ∘ (f ∘ assocˡ)
    ≈⟨ cancelInner f⁻¹∘f≈id ⟩
      assocʳ ∘ assocˡ
    ≈⟨ assocʳ∘assocˡ ⟩
      id
    ∎

  inAssocʳ′-inverse : ∀
    {f : a × (b × c) ⇨ a′ × (b′ × c′)} {f⁻¹ : a′ × (b′ × c′) ⇨ a × (b × c)} →
    f⁻¹ ∘ f ≈ id → inAssocʳ′ f⁻¹ ∘ inAssocʳ′ f ≈ id
  inAssocʳ′-inverse {f = f} {f⁻¹} f⁻¹∘f≈id =
    begin
      inAssocʳ′ f⁻¹ ∘ inAssocʳ′ f
    ≡⟨⟩
      (assocˡ ∘ f⁻¹ ∘ assocʳ) ∘ (assocˡ ∘ f ∘ assocʳ)
    ≈⟨ (∘≈ˡ ∘-assocˡ ; cancelInner assocʳ∘assocˡ) ⟩
      (assocˡ ∘ f⁻¹) ∘ (f ∘ assocʳ)
    ≈⟨ cancelInner f⁻¹∘f≈id ⟩
      assocˡ ∘ assocʳ
    ≈⟨ assocˡ∘assocʳ ⟩
      id
    ∎

  inAssocˡ-inverse : ∀ {c : obj} {f : a × b ⇨ a′ × b′} {f⁻¹ : a′ × b′ ⇨ a × b} →
    f⁻¹ ∘ f ≈ id → inAssocˡ {c = c} f⁻¹ ∘ inAssocˡ f ≈ id
  inAssocˡ-inverse {c = c} {f} {f⁻¹} f⁻¹∘f≈id =
    begin
      inAssocˡ {c = c} f⁻¹ ∘ inAssocˡ f
    ≡⟨⟩
      inAssocˡ′ (first f⁻¹) ∘ inAssocˡ′ (first f)
    ≈⟨ inAssocˡ′-inverse (first-inverse f⁻¹∘f≈id) ⟩
      id
    ∎

  inAssocʳ-inverse : ∀ {a : obj} {f : b × c ⇨ b′ × c′} {f⁻¹ : b′ × c′ ⇨ b × c} →
    f⁻¹ ∘ f ≈ id → inAssocʳ {a = a} f⁻¹ ∘ inAssocʳ f ≈ id
  inAssocʳ-inverse {a = a} {f} {f⁻¹} f⁻¹∘f≈id =
    begin
      inAssocʳ {a = a} f⁻¹ ∘ inAssocʳ f
    ≡⟨⟩
      inAssocʳ′ (second f⁻¹) ∘ inAssocʳ′ (second f)
    ≈⟨ inAssocʳ′-inverse (second-inverse f⁻¹∘f≈id) ⟩
      id
    ∎

  !⊗! : ∀ {a b : obj} → ! {a = a} ⊗ ! {a = b} ≈ unitorⁱʳ ∘ !
  !⊗! {a} {b} =
    begin
      ! ⊗ !
    ≡⟨⟩
      ! ∘ exl ▵ ! ∘ exr
    ≈⟨ ▵≈ ∀⊤ ∀⊤ ⟩
      ! ▵ !
    ≈⟨ sym≈ (▵≈ ∀⊤ ∀⊤) ⟩
      id ∘ ! ▵ ! ∘ !
    ≈⟨ sym≈ ▵∘ ⟩
      (id ▵ !) ∘ !
    ≡⟨⟩
      unitorⁱʳ ∘ !
    ∎

  [exl⊗exl]∘transpose : ∀ {a b c d : obj} →
    (exl ⊗ exl) ∘ transpose {a = a} {b} {c} {d} ≈ exl
  [exl⊗exl]∘transpose =
    begin
      (exl ⊗ exl) ∘ transpose
    ≡⟨⟩
      (exl ⊗ exl) ∘ ((exl ∘ exl ▵ exl ∘ exr) ▵ (exr ∘ exl ▵ exr ∘ exr))
    ≈⟨ ⊗∘▵ ⟩
      exl ∘ (exl ∘ exl ▵ exl ∘ exr) ▵ exl ∘ (exr ∘ exl ▵ exr ∘ exr)
    ≈⟨ ▵≈ exl∘▵ exl∘▵ ⟩
      exl ∘ exl ▵ exr ∘ exl
    ≈⟨ sym≈ ▵∘ ⟩
      (exl ▵ exr) ∘ exl
    ≈⟨ elimˡ exl▵exr ⟩
      exl
    ∎

  [exr⊗exr]∘transpose : ∀ {a b c d : obj} →
    (exr ⊗ exr) ∘ transpose {a = a} {b} {c} {d} ≈ exr
  [exr⊗exr]∘transpose =
    begin
      (exr ⊗ exr) ∘ transpose
    ≡⟨⟩
      (exr ⊗ exr) ∘ ((exl ∘ exl ▵ exl ∘ exr) ▵ (exr ∘ exl ▵ exr ∘ exr))
    ≈⟨ ⊗∘▵ ⟩
      exr ∘ (exl ∘ exl ▵ exl ∘ exr) ▵ exr ∘ (exr ∘ exl ▵ exr ∘ exr)
    ≈⟨ ▵≈ exr∘▵ exr∘▵ ⟩
      exl ∘ exr ▵ exr ∘ exr
    ≈⟨ sym≈ ▵∘ ⟩
      (exl ▵ exr) ∘ exr
    ≈⟨ elimˡ exl▵exr ⟩
      exr
    ∎

  transpose∘▵▵▵ : ∀ {a₁ c₁ c₂ d₁ d₂ : obj}
    {f₁ : a₁ ⇨ c₁} {f₂ : a₁ ⇨ c₂} {g₁ : a₁ ⇨ d₁} {g₂ : a₁ ⇨ d₂} →
    transpose ∘ ((f₁ ▵ f₂) ▵ (g₁ ▵ g₂)) ≈ (f₁ ▵ g₁) ▵ (f₂ ▵ g₂)
  transpose∘▵▵▵ {f₁ = f₁} {f₂} {g₁} {g₂} =
    begin
      transpose ∘ ((f₁ ▵ f₂) ▵ (g₁ ▵ g₂))
    ≡⟨⟩
      ((exl ∘ exl ▵ exl ∘ exr) ▵ (exr ∘ exl ▵ exr ∘ exr)) ∘
      ((f₁ ▵ f₂) ▵ (g₁ ▵ g₂))
    ≈⟨ ▵∘ ⟩
      (exl ∘ exl ▵ exl ∘ exr) ∘ ((f₁ ▵ f₂) ▵ (g₁ ▵ g₂)) ▵
      (exr ∘ exl ▵ exr ∘ exr) ∘ ((f₁ ▵ f₂) ▵ (g₁ ▵ g₂))
    ≈⟨ ▵≈ ▵∘ ▵∘ ⟩
      ((exl ∘ exl) ∘ ((f₁ ▵ f₂) ▵ (g₁ ▵ g₂)) ▵
       (exl ∘ exr) ∘ ((f₁ ▵ f₂) ▵ (g₁ ▵ g₂))) ▵
      ((exr ∘ exl) ∘ ((f₁ ▵ f₂) ▵ (g₁ ▵ g₂)) ▵
       (exr ∘ exr) ∘ ((f₁ ▵ f₂) ▵ (g₁ ▵ g₂)))
    ≈⟨ ▵≈ (▵≈ ∘-assocʳ ∘-assocʳ) (▵≈ ∘-assocʳ ∘-assocʳ) ⟩
      (exl ∘ exl ∘ ((f₁ ▵ f₂) ▵ (g₁ ▵ g₂)) ▵
       exl ∘ exr ∘ ((f₁ ▵ f₂) ▵ (g₁ ▵ g₂))) ▵
      (exr ∘ exl ∘ ((f₁ ▵ f₂) ▵ (g₁ ▵ g₂)) ▵
       exr ∘ exr ∘ ((f₁ ▵ f₂) ▵ (g₁ ▵ g₂)))
    ≈⟨ ▵≈ (▵≈ (∘≈ʳ exl∘▵) (∘≈ʳ exr∘▵)) (▵≈ (∘≈ʳ exl∘▵) (∘≈ʳ exr∘▵)) ⟩
      (exl ∘ (f₁ ▵ f₂) ▵ exl ∘ (g₁ ▵ g₂)) ▵ (exr ∘ (f₁ ▵ f₂) ▵ exr ∘ (g₁ ▵ g₂))
    ≈⟨ ▵≈ (▵≈ exl∘▵ exl∘▵) (▵≈ exr∘▵ exr∘▵) ⟩
      (f₁ ▵ g₁) ▵ (f₂ ▵ g₂)
    ∎

  transpose∘▵⊗▵ : ∀ {a₁ a₂ c₁ c₂ d₁ d₂ : obj}
    {f₁ : a₁ ⇨ c₁} {f₂ : a₂ ⇨ c₂} {g₁ : a₁ ⇨ d₁} {g₂ : a₂ ⇨ d₂} →
    transpose ∘ ((f₁ ⊗ f₂) ▵ (g₁ ⊗ g₂)) ≈ (f₁ ▵ g₁) ⊗ (f₂ ▵ g₂)
  transpose∘▵⊗▵ {f₁ = f₁} {f₂} {g₁} {g₂} =
    begin
      transpose ∘ ((f₁ ⊗ f₂) ▵ (g₁ ⊗ g₂))
    ≡⟨⟩
      transpose ∘ ((f₁ ∘ exl ▵ f₂ ∘ exr) ▵ (g₁ ∘ exl ▵ g₂ ∘ exr))
    ≈⟨ transpose∘▵▵▵ ⟩
      ((f₁ ∘ exl ▵ g₁ ∘ exl) ▵ (f₂ ∘ exr ▵ g₂ ∘ exr))
    ≈⟨ sym≈ (▵≈ ▵∘ ▵∘) ⟩
      ((f₁ ▵ g₁) ∘ exl ▵ (f₂ ▵ g₂) ∘ exr)
    ≡⟨⟩
      (f₁ ▵ g₁) ⊗ (f₂ ▵ g₂)
    ∎

  transpose∘transpose : ∀ {a b c d : obj} →
    transpose ∘ transpose {a = a} {b} {c} {d} ≈ id
  transpose∘transpose =
    begin
      transpose ∘ transpose
    ≡⟨⟩
      transpose ∘ ((exl ∘ exl ▵ exl ∘ exr) ▵ (exr ∘ exl ▵ exr ∘ exr))
    ≈⟨ transpose∘▵▵▵ ⟩
      ((exl ∘ exl ▵ exr ∘ exl) ▵ (exl ∘ exr ▵ exr ∘ exr))
    ≈⟨ sym≈ (▵≈ ▵∘ ▵∘) ⟩
      ((exl ▵ exr) ∘ exl ▵ (exl ▵ exr) ∘ exr)
    ≈⟨ ▵≈ (elimˡ exl▵exr) (elimˡ exl▵exr) ⟩
      exl ▵ exr
    ≈⟨ exl▵exr ⟩
      id
    ∎

open Assoc public
