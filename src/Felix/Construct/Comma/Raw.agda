{-# OPTIONS --safe --without-K #-}

open import Level

open import Felix.Raw
open import Felix.Equiv
open import Felix.Laws as L
       hiding (Category; Cartesian; CartesianClosed) -- ; Logic; Monoid
open import Felix.Homomorphism
open ≈-Reasoning
open import Felix.Reasoning

module Felix.Construct.Comma.Raw
   {o₀}{obj₀ : Set o₀} {ℓ₀} (_⇨₀_ : obj₀ → obj₀ → Set ℓ₀) ⦃ _ : Category _⇨₀_ ⦄
   {o₁}{obj₁ : Set o₁} {ℓ₁} (_⇨₁_ : obj₁ → obj₁ → Set ℓ₁) ⦃ _ : Category _⇨₁_ ⦄
   {o₂}{obj₂ : Set o₂} {ℓ₂} (_⇨₂_ : obj₂ → obj₂ → Set ℓ₂) ⦃ _ : Category _⇨₂_ ⦄
   {q} ⦃ _ : Equivalent q _⇨₀_ ⦄ ⦃ _ : L.Category _⇨₀_ ⦄
   ⦃ hₒ₁ : Homomorphismₒ obj₁ obj₀ ⦄ ⦃ h₁ : Homomorphism _⇨₁_ _⇨₀_ ⦄
     ⦃ catH₁ : CategoryH _⇨₁_ _⇨₀_ ⦄
   ⦃ hₒ₂ : Homomorphismₒ obj₂ obj₀ ⦄ ⦃ h₂ : Homomorphism _⇨₂_ _⇨₀_ ⦄
     ⦃ catH₂ : CategoryH _⇨₂_ _⇨₀_ ⦄
 where

open import Felix.Construct.Comma.Type _⇨₀_ _⇨₁_ _⇨₂_
       ⦃ catH₁ = catH₁ ⦄ ⦃ catH₂ = catH₂ ⦄
     public

open Obj

module comma-cat where

  -- variable a : Obj  --  "No instance of type CategoryH _⇨₂_ _⇨₀_ was found in scope."

  -- id′ : ∀ {a} → a ⇨ a
  -- id′ {a} = mk id id
  --   (begin
  --      h a ∘ Fₘ id
  --    ≈⟨ elimʳ F-id ⟩
  --      h a
  --    ≈⟨ introˡ F-id ⟩
  --      Fₘ id ∘ h a
  --    ∎)
  -- -- 4.5s

  id′ : ∀ {a} → a ⇨ a
  id′ = mk id id (elimʳ F-id ; introˡ F-id)

  -- comp : ∀ {a b c} → (b ⇨ c) → (a ⇨ b) → (a ⇨ c)
  -- comp {a}{b}{c} (mk g₁ g₂ comm-g) (mk f₁ f₂ comm-f) =
  --   mk (g₁ ∘ f₁) (g₂ ∘ f₂)
  --     (begin
  --        h c ∘ Fₘ (g₁ ∘ f₁)
  --      ≈⟨ ∘≈ʳ F-∘ ⟩
  --        h c ∘ (Fₘ g₁ ∘ Fₘ f₁)
  --      ≈⟨ ∘-assocˡ′ comm-g ⟩
  --        (Fₘ g₂ ∘ h b) ∘ Fₘ f₁
  --      ≈⟨ ∘-assocʳ′ comm-f ⟩
  --        Fₘ g₂ ∘ (Fₘ f₂ ∘ h a)
  --      ≈⟨ ∘-assocˡ′ (sym F-∘) ⟩
  --        Fₘ (g₂ ∘ f₂) ∘ h a
  --      ∎)
  -- -- 35s

  comp : ∀ {a b c} → (b ⇨ c) → (a ⇨ b) → (a ⇨ c)
  comp (mk g₁ g₂ comm-g) (mk f₁ f₂ comm-f) =
    mk (g₁ ∘ f₁) (g₂ ∘ f₂)
       (∘≈ʳ F-∘ ; ∘-assocˡ′ comm-g ; ∘-assocʳ′ comm-f ; ∘-assocˡ′ (sym F-∘))

  instance

    category : Category _⇨_
    category = record { id = id′ ; _∘_ = comp }

module comma-products
    ⦃ _ : Products obj₁ ⦄  ⦃ _ : Products obj₂ ⦄  ⦃ _ : Products obj₀ ⦄
    ⦃ _ : Cartesian _⇨₁_ ⦄ ⦃ _ : Cartesian _⇨₂_ ⦄ ⦃ _ : Cartesian _⇨₀_ ⦄
    ⦃ _ : L.Cartesian _⇨₀_ ⦄
    ⦃ _ : ProductsH obj₁ _⇨₀_ ⦄ ⦃ _ : ProductsH obj₂ _⇨₀_ ⦄
    ⦃ _ : StrongProductsH obj₁ _⇨₀_ ⦄ ⦃ _ : StrongProductsH obj₂ _⇨₀_ ⦄
    ⦃ _ : CartesianH _⇨₁_ _⇨₀_ ⦄ ⦃ _ : CartesianH _⇨₂_ _⇨₀_ ⦄
  where

  instance

    products : Products Obj
    products = record { ⊤   = mkO (ε ∘ ε⁻¹)
                      ; _×_ = λ (mkO h) (mkO k) → mkO (μ ∘ (h ⊗ k) ∘ μ⁻¹)
                      }

  -- !′ : ∀ {a} → a ⇨ ⊤
  -- !′ {a} = mk ! !
  --   (begin
  --      h ⊤ ∘ Fₘ !
  --    ≡⟨⟩
  --      (ε ∘ ε⁻¹) ∘ Fₘ !
  --    ≈⟨ ∘≈ʳ F-! ; cancelInner ε⁻¹∘ε ⟩
  --      ε ∘ !
  --    ≈⟨ ∘≈ʳ (sym ∀⊤) ⟩
  --      ε ∘ (! ∘ h a)
  --    ≈⟨ ∘-assocˡ′ (sym F-!) ⟩
  --      Fₘ ! ∘ h a
  --    ∎)
  -- -- 23s

  !′ : ∀ {a} → a ⇨ ⊤
  !′ = mk ! ! (∘≈ʳ F-! ; cancelInner ε⁻¹∘ε ; ∘≈ʳ (sym ∀⊤) ; ∘-assocˡ′ (sym F-!))

  -- fork : ∀ {a c d} → (a ⇨ c) → (a ⇨ d) → (a ⇨ c × d)
  -- fork {a}{c}{d} (mk f₁ f₂ comm-f) (mk g₁ g₂ comm-g) =
  --   mk (f₁ ▵ g₁) (f₂ ▵ g₂)
  --     (begin
  --        h (c × d) ∘ Fₘ (f₁ ▵ g₁)
  --      ≈⟨ ∘≈ ∘-assocˡ F-▵ ; cancelInner μ⁻¹∘μ ⟩
  --        (μ ∘ (h c ⊗ h d)) ∘ (Fₘ f₁ ▵ Fₘ g₁)
  --      ≈⟨ ∘-assocʳ′ (⊗∘▵ ; ▵≈ comm-f comm-g ; sym ▵∘) ⟩
  --        μ ∘ ((Fₘ f₂ ▵ Fₘ g₂) ∘ h a)
  --      ≈⟨ ∘-assocˡ′ (sym F-▵) ⟩
  --        Fₘ (f₂ ▵ g₂) ∘ h a
  --      ∎)
  -- -- 1m ?

  fork : ∀ {a c d} → (a ⇨ c) → (a ⇨ d) → (a ⇨ c × d)
  fork (mk f₁ f₂ comm-f) (mk g₁ g₂ comm-g) =
    mk (f₁ ▵ g₁) (f₂ ▵ g₂)
       ( ∘≈ ∘-assocˡ F-▵
       ; cancelInner μ⁻¹∘μ
       ; ∘-assocʳ′ (⊗∘▵ ; ▵≈ comm-f comm-g ; sym ▵∘)
       ; ∘-assocˡ′ (sym F-▵)
       )

  -- exl′ : ∀ {a b} → a × b ⇨ a
  -- exl′ {a}{b} = mk exl exl
  --   (begin
  --      h a ∘ Fₘ exl
  --    ≈⟨ ∘≈ʳ (introʳ μ∘μ⁻¹ ; ∘-assocˡ′ F-exl) ⟩
  --      h a ∘ (exl ∘ μ⁻¹)
  --    ≈⟨ ∘-assocˡʳ′ (sym exl∘▵) ⟩
  --      exl ∘ (h a ⊗ h b) ∘ μ⁻¹
  --    ≈⟨ sym (∘-assocˡ′ F-exl) ⟩
  --      Fₘ exl ∘ μ ∘ (h a ⊗ h b) ∘ μ⁻¹
  --    ∎)
  -- -- 45s

  exl′ : ∀ {a b} → a × b ⇨ a
  exl′ = mk exl exl
    ( ∘≈ʳ (introʳ μ∘μ⁻¹ ; ∘-assocˡ′ F-exl)
    ; ∘-assocˡʳ′ (sym exl∘▵)
    ; sym (∘-assocˡ′ F-exl)
    )

  -- exr′ : ∀ {a b} → a × b ⇨ b
  -- exr′ {a}{b} = mk exr exr
  --   (begin
  --      h b ∘ Fₘ exr
  --    ≈⟨ ∘≈ʳ (introʳ μ∘μ⁻¹ ; ∘-assocˡ′ F-exr) ⟩
  --      h b ∘ (exr ∘ μ⁻¹)
  --    ≈⟨ ∘-assocˡʳ′ (sym exr∘▵) ⟩
  --      exr ∘ (h a ⊗ h b) ∘ μ⁻¹
  --    ≈⟨ sym (∘-assocˡ′ F-exr) ⟩
  --      Fₘ exr ∘ μ ∘ (h a ⊗ h b) ∘ μ⁻¹
  --    ∎)
  -- -- 45s

  exr′ : ∀ {a b} → a × b ⇨ b
  exr′ = mk exr exr
    ( ∘≈ʳ (introʳ μ∘μ⁻¹ ; ∘-assocˡ′ F-exr)
    ; ∘-assocˡʳ′ (sym exr∘▵)
    ; sym (∘-assocˡ′ F-exr)
    )

  instance

    cartesian : Cartesian _⇨_
    cartesian = record { ! = !′ ; _▵_ = fork ; exl = exl′ ; exr = exr′ }


-- module comma-booleans
--     ⦃ _ : Products obj₁ ⦄  ⦃ _ : Products obj₂ ⦄  ⦃ _ : Products obj₀ ⦄
--     ⦃ _ : Cartesian _⇨₁_ ⦄ ⦃ _ : Cartesian _⇨₂_ ⦄ ⦃ _ : Cartesian _⇨₀_ ⦄
--     ⦃ _ : L.Cartesian _⇨₀_ ⦄
--     ⦃ _ : ProductsH obj₁ _⇨₀_ ⦄  ⦃ _ : ProductsH obj₂ _⇨₀_ ⦄
--     ⦃ _ : StrongProductsH obj₁ _⇨₀_ ⦄ ⦃ _ : StrongProductsH obj₂ _⇨₀_ ⦄
--     ⦃ _ : CartesianH _⇨₁_ _⇨₀_ ⦄ ⦃ _ : CartesianH _⇨₂_ _⇨₀_ ⦄
--     -- TODO: remove cartesian stuff as able
--     ⦃ _ : Boolean obj₁ ⦄  ⦃ _ : Boolean obj₂ ⦄  ⦃ _ : Boolean obj₀ ⦄
--     ⦃ _ : Logic _⇨₁_ ⦄ ⦃ _ : Logic _⇨₂_ ⦄ ⦃ _ : Logic _⇨₀_ ⦄
--     ⦃ _ : L.Logic _⇨₀_ ⦄
--     ⦃ _ : BooleanH obj₁ _⇨₀_ ⦄  ⦃ _ : BooleanH obj₂ _⇨₀_ ⦄
--     ⦃ _ : StrongBooleanH obj₁ _⇨₀_ ⦄  ⦃ _ : StrongBooleanH obj₂ _⇨₀_ ⦄
--     ⦃ _ : LogicH _⇨₁_ _⇨₀_ ⦄ ⦃ _ : LogicH _⇨₂_ _⇨₀_ ⦄
--  where

--   instance

--     boolean : Boolean Obj
--     boolean = record { Bool = mkO (β ∘ β⁻¹) }

--   -- false′ : ⊤ ⇨ Bool
--   -- false′ = mk false false
--   --   (begin
--   --     h Bool ∘ Fₘ false
--   --    ≡⟨⟩
--   --     (β ∘ β⁻¹) ∘ Fₘ false
--   --    ≈⟨ ∘≈ʳ F-false′ ⟩
--   --     (β ∘ β⁻¹) ∘ β ∘ false ∘ ε⁻¹
--   --    ≈⟨ ∘-assocˡ′ (∘-assoc-elimʳ β⁻¹∘β) ⟩
--   --     β ∘ false ∘ ε⁻¹
--   --    -- (β ∘ false) ∘ ε⁻¹
--   --    -- ((β ∘ false) ∘ ε⁻¹) ∘ (ε ∘ ε⁻¹)
--   --    -- (β ∘ false ∘ ε⁻¹) ∘ (ε ∘ ε⁻¹)
--   --    ≈˘⟨ (∘≈ˡ ∘-assocˡ ; cancelInner ε⁻¹∘ε ; ∘-assocʳ) ⟩
--   --     (β ∘ false ∘ ε⁻¹) ∘ (ε ∘ ε⁻¹)
--   --    ≈⟨ ∘≈ˡ (sym F-false′) ⟩
--   --     Fₘ false ∘ (ε ∘ ε⁻¹)
--   --    ≡⟨⟩
--   --     Fₘ false ∘ h ⊤
--   --    ∎)

--   false′ : ⊤ ⇨ Bool
--   false′ = mk false false
--     ( ∘≈ʳ F-false′
--     ; ∘-assocˡ′ (∘-assoc-elimʳ β⁻¹∘β)
--     ; sym (∘≈ˡ (F-false′ ; ∘-assocˡ) ; cancelInner ε⁻¹∘ε ; ∘-assocʳ)
--     )

--   true′ : ⊤ ⇨ Bool
--   true′ = mk true true
--     ( ∘≈ʳ F-true′
--     ; ∘-assocˡ′ (∘-assoc-elimʳ β⁻¹∘β)
--     ; sym (∘≈ˡ (F-true′ ; ∘-assocˡ) ; cancelInner ε⁻¹∘ε ; ∘-assocʳ)
--     )

--   -- not′ = mk not not
--   --   (begin
--   --      h Bool ∘ Fₘ not
--   --    ≡⟨⟩
--   --      (β ∘ β⁻¹) ∘ Fₘ not
--   --    ≈⟨ ∘≈ʳ F-not′ ⟩
--   --      (β ∘ β⁻¹) ∘ (β ∘ not ∘ β⁻¹)
--   --    ≈⟨ cancelInner β⁻¹∘β ⟩
--   --      β ∘ not ∘ β⁻¹
--   --    ≈⟨ sym (∘-assocˡʳ′ F-not) ⟩
--   --      Fₘ not ∘ (β ∘ β⁻¹)
--   --    ∎)

--   not′ : Bool ⇨ Bool
--   not′ = mk not not
--     ( ∘≈ʳ F-not′
--     ; cancelInner β⁻¹∘β
--     ; sym (∘-assocˡʳ′ F-not)
--     )

--   -- ∧′ : Bool × Bool ⇨ Bool
--   -- ∧′ = mk ∧ ∧
--   --   (begin
--   --      h Bool ∘ Fₘ ∧
--   --    ≡⟨⟩
--   --      (β ∘ β⁻¹) ∘ Fₘ ∧
--   --    ≈⟨ ∘≈ʳ F-∧′ ⟩
--   --      (β ∘ β⁻¹) ∘ β ∘ ∧ ∘ (β⁻¹ ⊗ β⁻¹) ∘ μ⁻¹
--   --    ≈⟨ ∘-assocˡ′ (∘-assoc-elimʳ β⁻¹∘β) ⟩
--   --      β ∘ ∧ ∘ (β⁻¹ ⊗ β⁻¹) ∘ μ⁻¹
--   --    ≈⟨ ∘-assocˡ′ (sym F-∧) ⟩
--   --      (Fₘ ∧ ∘ μ ∘ (β ⊗ β)) ∘ (β⁻¹ ⊗ β⁻¹) ∘ μ⁻¹
--   --    ≈⟨ ∘-assocʳ′ ∘-assocʳ ⟩
--   --      Fₘ ∧ ∘ μ ∘ (β ⊗ β) ∘ (β⁻¹ ⊗ β⁻¹) ∘ μ⁻¹
--   --    ≈⟨ ∘≈ʳ² (∘-assocˡ′ ⊗∘⊗) ⟩
--   --      Fₘ ∧ ∘ μ ∘ ((β ∘ β⁻¹) ⊗ (β ∘ β⁻¹)) ∘ μ⁻¹
--   --    ≡⟨⟩
--   --      Fₘ ∧ ∘ μ ∘ (h Bool ⊗ h Bool) ∘ μ⁻¹
--   --    ≡⟨⟩
--   --      Fₘ ∧ ∘ h (Bool × Bool)
--   --    ∎)

--   ∧′ : Bool × Bool ⇨ Bool
--   ∧′ = mk ∧ ∧
--           ( ∘≈ʳ F-∧′
--           ; ∘-assocˡ′ (∘-assoc-elimʳ β⁻¹∘β)
--           ; ∘-assocˡ′ (sym F-∧)
--           ; ∘-assocʳ′ ∘-assocʳ
--           ; ∘≈ʳ² (∘-assocˡ′ ⊗∘⊗)
--           )

--   ∨′ : Bool × Bool ⇨ Bool
--   ∨′ = mk ∨ ∨
--           ( ∘≈ʳ F-∨′
--           ; ∘-assocˡ′ (∘-assoc-elimʳ β⁻¹∘β)
--           ; ∘-assocˡ′ (sym F-∨)
--           ; ∘-assocʳ′ ∘-assocʳ
--           ; ∘≈ʳ² (∘-assocˡ′ ⊗∘⊗)
--           )

--   xor′ : Bool × Bool ⇨ Bool
--   xor′ = mk xor xor
--             ( ∘≈ʳ F-xor′
--             ; ∘-assocˡ′ (∘-assoc-elimʳ β⁻¹∘β)
--             ; ∘-assocˡ′ (sym F-xor)
--             ; ∘-assocʳ′ ∘-assocʳ
--             ; ∘≈ʳ² (∘-assocˡ′ ⊗∘⊗)
--             )

--   -- cond′ : ∀ {a} → Bool × (a × a) ⇨ a
--   -- cond′ {a} = mk cond cond
--   --   (begin
--   --      h a ∘ Fₘ cond
--   --    ≈⟨ ∘≈ʳ F-cond′ ⟩
--   --      h a ∘ cond ∘ (β⁻¹ ⊗ μ⁻¹) ∘ μ⁻¹
--   --    ≈⟨ ∘-assocˡ′ f∘cond ; ∘-assocʳ ⟩
--   --      cond ∘ second (h a ⊗ h a) ∘ (β⁻¹ ⊗ μ⁻¹) ∘ μ⁻¹
--   --    ≈⟨ ∘≈ʳ (∘-assocˡ′ ⊗∘⊗) ⟩
--   --      cond ∘ (id ∘ β⁻¹ ⊗ ((h a ⊗ h a) ∘ μ⁻¹)) ∘ μ⁻¹
--   --    ≈⟨ ∘≈ʳ (∘≈ˡ (⊗≈ˡ identityˡ)) ⟩
--   --      cond ∘ (β⁻¹ ⊗ ((h a ⊗ h a) ∘ μ⁻¹)) ∘ μ⁻¹
--   --    ≈⟨ ∘≈ˡ (sym F-cond) ⟩
--   --      (Fₘ cond ∘ μ ∘ (β ⊗ μ)) ∘ (β⁻¹ ⊗ ((h a ⊗ h a) ∘ μ⁻¹)) ∘ μ⁻¹
--   --    ≈⟨ ∘-assocʳ³ ⟩
--   --      Fₘ cond ∘ μ ∘ (β ⊗ μ) ∘ (β⁻¹ ⊗ ((h a ⊗ h a) ∘ μ⁻¹)) ∘ μ⁻¹
--   --    ≈⟨ ∘≈ʳ² ∘-assocˡ ⟩
--   --      Fₘ cond ∘ μ ∘ ((β ⊗ μ) ∘ (β⁻¹ ⊗ ((h a ⊗ h a) ∘ μ⁻¹))) ∘ μ⁻¹
--   --    ≈⟨ ∘≈ʳ² (∘≈ˡ ⊗∘⊗) ⟩
--   --      Fₘ cond ∘ μ ∘ ((β ∘ β⁻¹) ⊗ (μ ∘ (h a ⊗ h a) ∘ μ⁻¹)) ∘ μ⁻¹
--   --    ≡⟨⟩
--   --      Fₘ cond ∘ μ ∘ ((β ∘ β⁻¹) ⊗ h (a × a)) ∘ μ⁻¹
--   --    ≡⟨⟩
--   --      Fₘ cond ∘ μ ∘ (h Bool ⊗ h (a × a)) ∘ μ⁻¹
--   --    ≡⟨⟩
--   --      Fₘ cond ∘ h (Bool × (a × a))
--   --    ∎)

--   cond′ : ∀ {a} → Bool × (a × a) ⇨ a
--   cond′ {a} = mk cond cond
--     ( ∘≈ʳ F-cond′
--     ; ∘-assocˡ′ f∘cond ; ∘-assocʳ
--     ; ∘≈ʳ (∘-assocˡ′ ⊗∘⊗ ; ∘≈ˡ (⊗≈ˡ identityˡ))
--     ; ∘≈ˡ (sym F-cond)
--     ; ∘-assocʳ³
--     ; ∘≈ʳ² (∘-assocˡ ; ∘≈ˡ ⊗∘⊗)
--     )

--   instance

--     logic : Logic _⇨_
--     logic = record { false = false′
--                    ; true  = true′
--                    ; not   = not′
--                    ; ∧     = ∧′
--                    ; ∨     = ∨′
--                    ; xor   = xor′
--                    ; cond  = cond′
--                    }
