{-# OPTIONS --safe --without-K #-}

module Felix.Homomorphism where

open import Level
open import Function using () renaming (id to id′; _∘_ to _∘̇_)
-- Maybe import Felix.Raw for id & ∘ on functions

open import Felix.Equiv  public
open import Felix.Raw
open import Felix.Laws as L hiding (Category; Cartesian; Cocartesian ; CartesianClosed)
open import Felix.Reasoning

private
  variable
    o ℓ o₁ ℓ₁ o₂ ℓ₂ o₃ ℓ₃ : Level
    obj₁ obj₂ : Set o
    a b c d : obj₁

-- Category homomorphism (functor)
record CategoryH
  {obj₁ : Set o₁} (_⇨₁_ : obj₁ → obj₁ → Set ℓ₁) {q₁} ⦃ eq₁ : Equivalent q₁ _⇨₁_ ⦄
  {obj₂ : Set o₂} (_⇨₂_ : obj₂ → obj₂ → Set ℓ₂) {q₂} ⦃ eq₂ : Equivalent q₂ _⇨₂_ ⦄
  ⦃ _ : Category _⇨₁_ ⦄ ⦃ _ : Category _⇨₂_ ⦄
  ⦃ Hₒ : Homomorphismₒ obj₁ obj₂ ⦄
  ⦃ H : Homomorphism _⇨₁_ _⇨₂_ ⦄
       : Set (o₁ ⊔ ℓ₁ ⊔ q₁ ⊔ o₂ ⊔ ℓ₂ ⊔ q₂) where
  field
    F-cong : ∀ {a b} {f g : a ⇨₁ b} → f ≈ g → Fₘ f ≈ Fₘ g
    F-id : Fₘ (id {_⇨_ = _⇨₁_}{a = a}) ≈ id
    F-∘  : ∀ {a b c} {g : b ⇨₁ c} {f : a ⇨₁ b} → Fₘ (g ∘ f) ≈ Fₘ g ∘ Fₘ f
    -- TODO: make g and f explicit arguments? Wait and see.

  module _ ⦃ _ : L.Category _⇨₂_ ⦄ where
    open ≈-Reasoning ⦃ eq₂ ⦄

    F-∘³ : {a₀ a₁ a₂ a₃ : obj₁}
           {f₁ : a₀ ⇨₁ a₁}{f₂ : a₁ ⇨₁ a₂}{f₃ : a₂ ⇨₁ a₃}
         → Fₘ (f₃ ∘ f₂ ∘ f₁) ≈ Fₘ f₃ ∘ Fₘ f₂ ∘ Fₘ f₁
    F-∘³ = F-∘ ; ∘≈ʳ F-∘

    F-∘⁴ : {a₀ a₁ a₂ a₃ a₄ : obj₁}
           {f₁ : a₀ ⇨₁ a₁}{f₂ : a₁ ⇨₁ a₂}{f₃ : a₂ ⇨₁ a₃}{f₄ : a₃ ⇨₁ a₄}
         → Fₘ (f₄ ∘ f₃ ∘ f₂ ∘ f₁) ≈ Fₘ f₄ ∘ Fₘ f₃ ∘ Fₘ f₂ ∘ Fₘ f₁
    F-∘⁴ = F-∘ ; ∘≈ʳ F-∘³

    F-∘⁵ : {a₀ a₁ a₂ a₃ a₄ a₅ : obj₁}
           {f₁ : a₀ ⇨₁ a₁}{f₂ : a₁ ⇨₁ a₂}{f₃ : a₂ ⇨₁ a₃}{f₄ : a₃ ⇨₁ a₄}
             {f₅ : a₄ ⇨₁ a₅}
         → Fₘ (f₅ ∘ f₄ ∘ f₃ ∘ f₂ ∘ f₁) ≈ Fₘ f₅ ∘ Fₘ f₄ ∘ Fₘ f₃ ∘ Fₘ f₂ ∘ Fₘ f₁
    F-∘⁵ = F-∘ ; ∘≈ʳ F-∘⁴

    F-∘⁶ : {a₀ a₁ a₂ a₃ a₄ a₅ a₆ : obj₁}
           {f₁ : a₀ ⇨₁ a₁}{f₂ : a₁ ⇨₁ a₂}{f₃ : a₂ ⇨₁ a₃}{f₄ : a₃ ⇨₁ a₄}
             {f₅ : a₄ ⇨₁ a₅}{f₆ : a₅ ⇨₁ a₆}
         → Fₘ (f₆ ∘ f₅ ∘ f₄ ∘ f₃ ∘ f₂ ∘ f₁) ≈
           Fₘ f₆ ∘ Fₘ f₅ ∘ Fₘ f₄ ∘ Fₘ f₃ ∘ Fₘ f₂ ∘ Fₘ f₁
    F-∘⁶ = F-∘ ; ∘≈ʳ F-∘⁵

open CategoryH ⦃ … ⦄ public

id-CategoryH : {obj : Set o} {_⇨_ : obj → obj → Set ℓ}
               {q : Level} ⦃ _ : Equivalent q _⇨_ ⦄
               ⦃ _ : Category _⇨_ ⦄
             → CategoryH _⇨_ _⇨_ ⦃ Hₒ = id-Hₒ ⦄ ⦃ H = id-H ⦄
id-CategoryH = record { F-cong = id′ ; F-id = refl≈ ; F-∘ = refl≈ }
  where open ≈-Reasoning

infixr 9 _∘-CategoryH_
_∘-CategoryH_ :
   {obj₁ : Set o₁} {_⇨₁_ : obj₁ → obj₁ → Set ℓ₁}
   {obj₂ : Set o₂} {_⇨₂_ : obj₂ → obj₂ → Set ℓ₂}
   {obj₃ : Set o₃} {_⇨₃_ : obj₃ → obj₃ → Set ℓ₃}
   {q₁ : Level} ⦃ eq₁ : Equivalent q₁ _⇨₁_ ⦄
   {q₂ : Level} ⦃ eq₂ : Equivalent q₂ _⇨₂_ ⦄
   {q₃ : Level} ⦃ eq₃ : Equivalent q₃ _⇨₃_ ⦄
   ⦃ _ : Category _⇨₁_ ⦄ ⦃ _ : Category _⇨₂_ ⦄ ⦃ _ : Category _⇨₃_ ⦄
   ⦃ Fₒ : Homomorphismₒ obj₁ obj₂ ⦄ ⦃ Fₘ : Homomorphism _⇨₁_ _⇨₂_ ⦄
   ⦃ Gₒ : Homomorphismₒ obj₂ obj₃ ⦄ ⦃ Gₘ : Homomorphism _⇨₂_ _⇨₃_ ⦄
   (G : CategoryH _⇨₂_ _⇨₃_) (F : CategoryH _⇨₁_ _⇨₂_)
  → CategoryH _⇨₁_ _⇨₃_ ⦃ Hₒ = Gₒ ∘Hₒ Fₒ ⦄ ⦃ H = Gₘ ∘H Fₘ ⦄
_∘-CategoryH_ ⦃ eq₃ = eq₃ ⦄ G F = record
  { F-cong = G.F-cong ∘̇ F.F-cong
  ; F-id   = G.F-cong F.F-id ; G.F-id
  ; F-∘    = G.F-cong F.F-∘  ; G.F-∘
  } where module F = CategoryH F
          module G = CategoryH G
          open ≈-Reasoning ⦃ eq₃ ⦄

open import Data.Product using (_,_) renaming (_×_ to _×̇_; <_,_> to _▵̇_)

-- infixr 7 _▵-CategoryH_
-- _▵-CategoryH_ :
--    {obj₁ : Set o₁} {_⇨₁_ : obj₁ → obj₁ → Set ℓ₁}
--    {obj₂ : Set o₂} {_⇨₂_ : obj₂ → obj₂ → Set ℓ₂}
--    {obj₃ : Set o₃} {_⇨₃_ : obj₃ → obj₃ → Set ℓ₃}
--    {q₁ : Level} ⦃ _ : Equivalent q₁ _⇨₁_ ⦄
--    {q₂ : Level} ⦃ _ : Equivalent q₂ _⇨₂_ ⦄
--    {q₃ : Level} ⦃ _ : Equivalent q₃ _⇨₃_ ⦄
--    ⦃ _ : Category _⇨₁_ ⦄ ⦃ _ : Category _⇨₂_ ⦄ ⦃ _ : Category _⇨₃_ ⦄
--    ⦃ Fₒ : Homomorphismₒ obj₁ obj₂ ⦄ ⦃ Fₘ : Homomorphism _⇨₁_ _⇨₂_ ⦄
--    ⦃ Gₒ : Homomorphismₒ obj₁ obj₃ ⦄ ⦃ Gₘ : Homomorphism _⇨₁_ _⇨₃_ ⦄
--    (F : CategoryH _⇨₁_ _⇨₂_) (G : CategoryH _⇨₁_ _⇨₃_)
--   → CategoryH _⇨₁_ (λ (a₂ , a₃) (b₂ , b₃) → (a₂ ⇨₂ b₂) ×̇ (a₃ ⇨₃ b₃)) ⦃ Hₒ = Fₒ ▵Hₒ Gₒ ⦄ ⦃ H = Fₘ ▵H Gₘ ⦄
-- G ▵-CategoryH F  = record
--   { F-cong = ? -- G.F-cong ▵̇ F.F-cong
--   ; F-id   = ? -- G.F-cong F.F-id ; G.F-id
--   ; F-∘    = ? -- G.F-cong F.F-∘  ; G.F-∘
--   }
--  where module F = CategoryH F ; module G = CategoryH G


record ProductsH
    (obj₁ : Set o₁) ⦃ _ : Products obj₁ ⦄
    {obj₂ : Set o₂} ⦃ _ : Products obj₂ ⦄
    (_⇨₂′_ : obj₂ → obj₂ → Set ℓ₂)
    ⦃ Hₒ : Homomorphismₒ obj₁ obj₂ ⦄
    : Set (o₁ ⊔ o₂ ⊔ ℓ₂) where
  private infix 0 _⇨₂_; _⇨₂_ = _⇨₂′_
  field
    -- https://ncatlab.org/nlab/show/monoidal+functor
    ε : ⊤ ⇨₂ Fₒ ⊤
    μ : {a b : obj₁} → Fₒ a × Fₒ b ⇨₂ Fₒ (a × b)

    ε⁻¹ : Fₒ ⊤ ⇨₂ ⊤
    μ⁻¹ : {a b : obj₁} → Fₒ (a × b) ⇨₂ Fₒ a × Fₒ b

open ProductsH ⦃ … ⦄ public

id-ProductsH : ∀ {obj : Set o} ⦃ _ : Products obj ⦄
                 {_⇨_ : obj → obj → Set ℓ} ⦃ _ : Category _⇨_ ⦄
             → ProductsH obj _⇨_ ⦃ Hₒ = id-Hₒ ⦄
id-ProductsH =
  record { ε = id ; μ = id ; ε⁻¹ = id ; μ⁻¹ = id }

record StrongProductsH
    (obj₁ : Set o₁) ⦃ _ : Products obj₁ ⦄
    {obj₂ : Set o₂} ⦃ _ : Products obj₂ ⦄
    (_⇨₂′_ : obj₂ → obj₂ → Set ℓ₂) ⦃ _ : Category _⇨₂′_ ⦄
    ⦃ Hₒ : Homomorphismₒ obj₁ obj₂ ⦄
    {q} ⦃ _ : Equivalent q _⇨₂′_ ⦄
    ⦃ pH : ProductsH obj₁ _⇨₂′_ ⦄
    : Set (o₁ ⊔ o₂ ⊔ ℓ₂ ⊔ q) where
  private infix 0 _⇨₂_; _⇨₂_ = _⇨₂′_
  field

    ε⁻¹∘ε : ε⁻¹ ∘ ε ≈ id
    ε∘ε⁻¹ : ε ∘ ε⁻¹ ≈ id

    μ⁻¹∘μ : {a b : obj₁} → μ⁻¹ ∘ μ {a = a}{b} ≈ id
    μ∘μ⁻¹ : {a b : obj₁} → μ ∘ μ⁻¹ {a = a}{b} ≈ id

open StrongProductsH ⦃ … ⦄ public

id-StrongProductsH :
  ∀ {obj : Set o} ⦃ _ : Products obj ⦄
  {_⇨_ : obj → obj → Set ℓ} ⦃ _ : Category _⇨_ ⦄
  {q} ⦃ _ : Equivalent q _⇨_ ⦄ ⦃ _ : L.Category _⇨_ ⦄
  → StrongProductsH obj _⇨_ ⦃ Hₒ = id-Hₒ ⦄ ⦃ pH = id-ProductsH ⦄
id-StrongProductsH =
  record { ε⁻¹∘ε = L.identityˡ ; ε∘ε⁻¹ = L.identityˡ
         ; μ⁻¹∘μ = L.identityˡ ; μ∘μ⁻¹ = L.identityˡ
         }

-- TODO: Try defining id-ProductsH via id-ProductsH′.

-- TODO: Try defining an instance module in place of id-ProductsH′ and
-- id-StrongProductsH′. Ditto for id-ProductsH and id-StrongProductsH.

-- Cartesian homomorphism (cartesian functor)
record CartesianH
  {obj₁ : Set o₁} ⦃ _ : Products obj₁ ⦄ (_⇨₁_ : obj₁ → obj₁ → Set ℓ₁)
  {obj₂ : Set o₂} ⦃ _ : Products obj₂ ⦄ (_⇨₂_ : obj₂ → obj₂ → Set ℓ₂)
  {q₁} ⦃ eq₁ : Equivalent q₁ _⇨₁_ ⦄ {q₂} ⦃ eq₂ : Equivalent q₂ _⇨₂_ ⦄
  ⦃ _ : Category _⇨₁_ ⦄ ⦃ _ : Cartesian _⇨₁_ ⦄
  ⦃ _ : Category _⇨₂_ ⦄ ⦃ _ : Cartesian _⇨₂_ ⦄
  ⦃ Hₒ : Homomorphismₒ obj₁ obj₂ ⦄
  ⦃ H : Homomorphism _⇨₁_ _⇨₂_ ⦄
  ⦃ pH : ProductsH obj₁ _⇨₂_ ⦄
       : Set (o₁ ⊔ ℓ₁ ⊔ q₁ ⊔ o₂ ⊔ ℓ₂ ⊔ q₂) where
  field
    F-!   : ∀ {a : obj₁} → Fₘ {a = a} ! ≈ ε ∘ !
    F-▵   : ∀ {a c d} {f : a ⇨₁ c}{g : a ⇨₁ d} → Fₘ (f ▵ g) ≈ μ ∘ (Fₘ f ▵ Fₘ g)
    F-exl : ∀ {a b : obj₁} → Fₘ exl ∘ μ {a = a}{b} ≈ exl
    F-exr : ∀ {a b : obj₁} → Fₘ exr ∘ μ {a = a}{b} ≈ exr

  module _ ⦃ _ : L.Category _⇨₂_ ⦄ ⦃ spH : StrongProductsH obj₁ _⇨₂_ ⦄ where
    open ≈-Reasoning ⦃ eq₂ ⦄

    F-!′ : {a : obj₁} → ε⁻¹ ∘ Fₘ {a = a} ! ≈ !
    F-!′ = ∘≈ʳ F-! ; ∘-assoc-elimˡ ε⁻¹∘ε

    F-▵′ : {f : a ⇨₁ c}{g : a ⇨₁ d} → μ⁻¹ ∘ Fₘ (f ▵ g) ≈ Fₘ f ▵ Fₘ g
    F-▵′ = ∘≈ʳ F-▵ ; ∘-assoc-elimˡ μ⁻¹∘μ

    F-exl′ : {a b : obj₁} → Fₘ exl ≈ exl ∘ μ⁻¹ {a = a}{b}
    F-exl′ = introʳ μ∘μ⁻¹ ; ∘-assocˡ′ F-exl

    F-exr′ : {a b : obj₁} → Fₘ exr ≈ exr ∘ μ⁻¹ {a = a}{b}
    F-exr′ = introʳ μ∘μ⁻¹ ; ∘-assocˡ′ F-exr

    module _ ⦃ _ : L.Cartesian _⇨₂_ ⦄ ⦃ _ : CategoryH _⇨₁_ _⇨₂_ ⦄ where

      F-⊗ : ∀ {a b c d}{f : a ⇨₁ c}{g : b ⇨₁ d} → Fₘ (f ⊗ g) ∘ μ ≈ μ ∘ (Fₘ f ⊗ Fₘ g)
      F-⊗ {f = f}{g} =
        begin
          Fₘ (f ∘ exl ▵ g ∘ exr) ∘ μ
        ≈⟨ ∘≈ˡ (F-▵ ; ∘≈ʳ (▵≈ F-∘ F-∘)) ⟩
          (μ ∘ (Fₘ f ∘ Fₘ exl ▵ Fₘ g ∘ Fₘ exr)) ∘ μ
        ≈⟨ ∘-assocʳ ⟩
          μ ∘ ((Fₘ f ∘ Fₘ exl ▵ Fₘ g ∘ Fₘ exr) ∘ μ)
        ≈⟨ ∘≈ʳ (▵∘ ; ▵≈ (∘-assocʳ′ F-exl) (∘-assocʳ′ F-exr)) ⟩
          μ ∘ (Fₘ f ∘ exl ▵ Fₘ g ∘ exr)
        ∎

      -- I wonder whether proofs become simpler and/or more regular if we switch
      -- all axioms and lemmas to the form "Fₘ ... ≈ ...". One experiment:
      F-⊗′ : ∀ {a b c d}{f : a ⇨₁ c}{g : b ⇨₁ d} → Fₘ (f ⊗ g) ≈ μ ∘ (Fₘ f ⊗ Fₘ g) ∘ μ⁻¹
      F-⊗′ {f = f}{g} =
        begin
          Fₘ (f ∘ exl ▵ g ∘ exr)
        ≈⟨ F-▵ ; ∘≈ʳ (▵≈ F-∘ F-∘) ⟩
          μ ∘ (Fₘ f ∘ Fₘ exl ▵ Fₘ g ∘ Fₘ exr)
        ≈⟨ ∘≈ʳ (▵≈ (∘≈ʳ F-exl′ ; ∘-assocˡ) (∘≈ʳ F-exr′ ; ∘-assocˡ)) ⟩
          μ ∘ ((Fₘ f ∘ exl) ∘ μ⁻¹ ▵ (Fₘ g ∘ exr) ∘ μ⁻¹)
        ≈⟨ ∘≈ʳ (sym≈ ▵∘) ⟩
          μ ∘ (Fₘ f ∘ exl ▵ Fₘ g ∘ exr) ∘ μ⁻¹
        ∎

      F-first : ∀ {a b c : obj₁}{f : a ⇨₁ c}
               → Fₘ (first {b = b} f) ∘ μ ≈ μ ∘ first (Fₘ f)
      F-first = F-⊗ ; ∘≈ʳ (⊗≈ʳ F-id)

      F-first′ : ∀ {a b c : obj₁}{f : a ⇨₁ c}
               → Fₘ (first {b = b} f) ≈ μ ∘ first (Fₘ f) ∘ μ⁻¹
      F-first′ = introʳ μ∘μ⁻¹ ; ∘-assocˡʳ′ F-first

      F-second : ∀ {a b d : obj₁}{g : b ⇨₁ d}
               → Fₘ (second {a = a} g) ∘ μ ≈ μ ∘ second (Fₘ g)
      F-second = F-⊗ ; ∘≈ʳ (⊗≈ˡ F-id)

      F-second′ : ∀ {a b d : obj₁}{g : b ⇨₁ d}
                → Fₘ (second {a = a} g) ≈ μ ∘ second (Fₘ g) ∘ μ⁻¹
      F-second′ = F-⊗′ ; ∘≈ʳ (∘≈ˡ (⊗≈ˡ F-id))

      F-assocˡ : ∀ {a b c : obj₁}
         → Fₘ (assocˡ {a = a}{b}{c}) ∘ μ ∘ second μ ≈ μ ∘ first μ ∘ assocˡ
      F-assocˡ =
        begin
          Fₘ assocˡ ∘ μ ∘ second μ
        ≡⟨⟩
          Fₘ (second exl ▵ exr ∘ exr) ∘ μ ∘ second μ
        ≈⟨ ∘≈ˡ F-▵ ⟩
          (μ ∘ (Fₘ (second exl) ▵ Fₘ (exr ∘ exr))) ∘ μ ∘ second μ
        ≈⟨ ∘-assocˡ′ (∘-assocʳ′ ▵∘ ; ∘≈ʳ (▵≈ʳ (∘≈ˡ F-∘ ; ∘-assocʳ′ F-exr))) ⟩
          (μ ∘ (Fₘ (second exl) ∘ μ ▵ Fₘ exr ∘ exr)) ∘ second μ
        ≈⟨ ∘-assocʳ′ (▵∘ ; ▵≈ ∘-assocʳ ∘-assocʳ ; ▵≈ʳ (∘≈ʳ exr∘▵ ; ∘-assocˡ′ F-exr)) ⟩
          μ ∘ (Fₘ (second exl) ∘ μ ∘ second μ ▵ exr ∘ exr)
        ≈⟨ ∘≈ʳ (▵≈ˡ (∘-assocˡ′ F-second)) ⟩
          μ ∘ ((μ ∘ second (Fₘ exl)) ∘ second μ ▵ exr ∘ exr)
        ≈⟨ ∘≈ʳ (▵≈ˡ (∘-assocʳ′ (second∘⊗ ; ⊗≈ʳ F-exl))) ⟩
          μ ∘ (μ ∘ second exl ▵ exr ∘ exr)
        ≈⟨ ∘≈ʳ (sym≈ first∘▵) ⟩
          μ ∘ first μ ∘ (second exl ▵ exr ∘ exr)
        ≡⟨⟩
          μ ∘ first μ ∘ assocˡ
        ∎

      F-assocˡ′ : ∀ {a b c : obj₁}
         → Fₘ (assocˡ {a = a}{b}{c}) ≈ μ ∘ first μ ∘ assocˡ ∘ second μ⁻¹ ∘ μ⁻¹
      F-assocˡ′ =
        begin
          Fₘ assocˡ
        ≈⟨ sym≈ (∘≈ʳ (∘≈ʳ (∘-assocˡ ; elimˡ (second-inverse μ∘μ⁻¹))) ; elimʳ μ∘μ⁻¹) ⟩
          Fₘ assocˡ ∘ μ ∘ second μ ∘ second μ⁻¹ ∘ μ⁻¹
        ≈⟨ ∘-assocˡ³ ; ∘≈ˡ F-assocˡ ; ∘-assocʳ³ ⟩
          μ ∘ first μ ∘ assocˡ ∘ second μ⁻¹ ∘ μ⁻¹
        ∎

      F-assocʳ : ∀ {a b c : obj₁}
         → Fₘ (assocʳ {a = a}{b}{c}) ∘ μ ∘ first μ ≈ μ ∘ second μ ∘ assocʳ
      F-assocʳ =
        begin
          Fₘ assocʳ ∘ μ ∘ first μ
        ≡⟨⟩
          Fₘ (exl ∘ exl ▵ first exr) ∘ μ ∘ first μ
        ≈⟨ ∘≈ˡ F-▵ ⟩
          (μ ∘ (Fₘ (exl ∘ exl) ▵ Fₘ (first exr))) ∘ μ ∘ first μ
        ≈⟨ ∘-assocʳ ⟩
          μ ∘ (Fₘ (exl ∘ exl) ▵ Fₘ (first exr)) ∘ μ ∘ first μ
        ≈⟨ ∘≈ʳ ∘-assocˡ ⟩
          μ ∘ ((Fₘ (exl ∘ exl) ▵ Fₘ (first exr)) ∘ μ) ∘ first μ
        ≈⟨ ∘≈ʳ (∘≈ˡ ▵∘) ⟩
          μ ∘ (Fₘ (exl ∘ exl) ∘ μ ▵ Fₘ (first exr) ∘ μ) ∘ first μ
        ≈⟨ ∘≈ʳ (∘≈ˡ (▵≈ (∘≈ˡ F-∘ ; ∘-assocʳ) F-first)) ⟩
          μ ∘ (Fₘ exl ∘ Fₘ exl ∘ μ ▵ μ ∘ first (Fₘ exr)) ∘ first μ
        ≈⟨ ∘≈ʳ ▵∘ ⟩
          μ ∘ ((Fₘ exl ∘ Fₘ exl ∘ μ) ∘ first μ ▵ (μ ∘ first (Fₘ exr)) ∘ first μ)
        ≈⟨ ∘≈ʳ (▵≈ ∘-assocʳ³ ∘-assocʳ) ⟩
          μ ∘ (Fₘ exl ∘ Fₘ exl ∘ μ ∘ first μ ▵ μ ∘ first (Fₘ exr) ∘ first μ)
        ≈⟨ ∘≈ʳ (▵≈ʳ (∘≈ʳ first∘first)) ⟩
          μ ∘ (Fₘ exl ∘ Fₘ exl ∘ μ ∘ first μ ▵ μ ∘ first (Fₘ exr ∘ μ))
        ≈⟨ ∘≈ʳ (▵≈ (∘≈ʳ ( ∘-assocˡ′ F-exl)) (∘≈ʳ (⊗≈ˡ F-exr))) ⟩
          μ ∘ (Fₘ exl ∘ exl ∘ first μ ▵ μ ∘ first exr)
        ≈⟨ ∘≈ʳ (▵≈ˡ (∘≈ʳ exl∘first)) ⟩
          μ ∘ (Fₘ exl ∘ μ ∘ exl ▵ μ ∘ first exr)
        ≈⟨ ∘≈ʳ (▵≈ˡ (∘-assocˡ′ F-exl)) ⟩
          μ ∘ (exl ∘ exl ▵ μ ∘ first exr)
        ≈⟨ ∘≈ʳ (sym≈ second∘▵) ⟩
          μ ∘ second μ ∘ (exl ∘ exl ▵ first exr)
        ≡⟨⟩
          μ ∘ second μ ∘ assocʳ
        ∎

      F-assocʳ′ : ∀ {a b c : obj₁}
         → Fₘ (assocʳ {a = a}{b}{c}) ≈ μ ∘ second μ ∘ assocʳ ∘ first μ⁻¹ ∘ μ⁻¹
      F-assocʳ′ =
        begin
          Fₘ assocʳ
        ≈⟨ sym≈ (∘≈ʳ (∘≈ʳ (∘-assocˡ ; elimˡ (first-inverse μ∘μ⁻¹))) ; elimʳ μ∘μ⁻¹) ⟩
          Fₘ assocʳ ∘ μ ∘ first μ ∘ first μ⁻¹ ∘ μ⁻¹
        ≈⟨ (∘-assocˡ³ ; ∘≈ˡ F-assocʳ ; ∘-assocʳ³) ⟩
          μ ∘ second μ ∘ assocʳ ∘ first μ⁻¹ ∘ μ⁻¹
        ∎

open CartesianH ⦃ … ⦄ public

id-CartesianH :
    {obj : Set o} {_⇨_ : obj → obj → Set ℓ} ⦃ _ : Products obj ⦄
    {q : Level} ⦃ _ : Equivalent q _⇨_ ⦄
    ⦃ _ :   Category _⇨_ ⦄ ⦃ _ :   Cartesian _⇨_ ⦄
    ⦃ _ : L.Category _⇨_ ⦄ ⦃ _ : L.Cartesian _⇨_ ⦄
  → CartesianH _⇨_ _⇨_ ⦃ Hₒ = id-Hₒ ⦄ ⦃ H = id-H ⦄ ⦃ pH = id-ProductsH ⦄
id-CartesianH = record
  { F-!   = sym≈ identityˡ
  ; F-▵   = sym≈ identityˡ
  ; F-exl = identityʳ
  ; F-exr = identityʳ
  } where open ≈-Reasoning


record CoproductsH
    (obj₁ : Set o₁) ⦃ _ : Coproducts obj₁ ⦄
    {obj₂ : Set o₂} ⦃ _ : Coproducts obj₂ ⦄
    (_⇨₂′_ : obj₂ → obj₂ → Set ℓ₂)
    ⦃ Hₒ : Homomorphismₒ obj₁ obj₂ ⦄
    : Set (o₁ ⊔ o₂ ⊔ ℓ₂) where
  private infix 0 _⇨₂_; _⇨₂_ = _⇨₂′_
  field
    δ⁻¹ : ⊥ ⇨₂ Fₒ ⊥
    ν⁻¹ : {a b : obj₁} → Fₒ a ⊎ Fₒ b ⇨₂ Fₒ (a ⊎ b)

    δ : Fₒ ⊥ ⇨₂ ⊥
    ν : {a b : obj₁} → Fₒ (a ⊎ b) ⇨₂ Fₒ a ⊎ Fₒ b

open CoproductsH ⦃ … ⦄ public

id-CoproductsH :
  {obj : Set o} ⦃ _ : Coproducts obj ⦄
  {_⇨_ : obj → obj → Set ℓ} ⦃ _ : Category _⇨_ ⦄ →
  CoproductsH obj _⇨_ ⦃ Hₒ = id-Hₒ ⦄
id-CoproductsH = record { δ = id ; ν = id ; δ⁻¹ = id ; ν⁻¹ = id }

-- Cocartesian homomorphism (cocartesian functor)
record CocartesianH
         {obj₁ : Set o₁} ⦃ _ : Coproducts obj₁ ⦄ (_⇨₁_ : obj₁ → obj₁ → Set ℓ₁)
         {obj₂ : Set o₂} ⦃ _ : Coproducts obj₂ ⦄ (_⇨₂_ : obj₂ → obj₂ → Set ℓ₂)
         {q} ⦃ _ : Equivalent q _⇨₂_ ⦄
         ⦃ _ : Category _⇨₁_ ⦄ ⦃ _ : Cocartesian _⇨₁_ ⦄
         ⦃ _ : Category _⇨₂_ ⦄ ⦃ _ : Cocartesian _⇨₂_ ⦄
         ⦃ Hₒ : Homomorphismₒ obj₁ obj₂ ⦄
         ⦃ H : Homomorphism _⇨₁_ _⇨₂_ ⦄
         ⦃ pH : CoproductsH obj₁ _⇨₂_ ⦄
       : Set (o₁ ⊔ ℓ₁ ⊔ o₂ ⊔ ℓ₂ ⊔ q) where
  field
    F-¡   : ∀ {b : obj₁} → Fₘ {b = b} ¡ ≈ ¡ ∘ δ
    F-▿   : ∀ {a b c} {f : a ⇨₁ c} {g : b ⇨₁ c} → Fₘ (f ▿ g) ≈ (Fₘ f ▿ Fₘ g) ∘ ν
    F-inl : ∀ {a b : obj₁} → ν {a = a}{b} ∘ Fₘ inl ≈ inl
    F-inr : ∀ {a b : obj₁} → ν {a = a}{b} ∘ Fₘ inr ≈ inr

open CocartesianH ⦃ … ⦄ public


record ExponentialsH
    (obj₁ : Set o₁) ⦃ _ : Exponentials obj₁ ⦄
    {obj₂ : Set o₂} ⦃ _ : Exponentials obj₂ ⦄ (_⇨₂′_ : obj₂ → obj₂ → Set ℓ₂)
    ⦃ Hₒ : Homomorphismₒ obj₁ obj₂ ⦄
    : Set (o₁ ⊔ o₂ ⊔ ℓ₂) where
  private infix 0 _⇨₂_; _⇨₂_ = _⇨₂′_
  field
    ζ : {a b : obj₁} → (Fₒ a ⇛ Fₒ b) ⇨₂ Fₒ (a ⇛ b)
    -- *Strong*?
    ζ⁻¹ : {a b : obj₁} → Fₒ (a ⇛ b) ⇨₂ (Fₒ a ⇛ Fₒ b)

open ExponentialsH ⦃ … ⦄ public

-- TODO: CartesianClosedH
