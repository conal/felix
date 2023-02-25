{-# OPTIONS --safe --without-K #-}
-- Product of categories

open import Felix.Object
open import Felix.Raw
open import Felix.Homomorphism
open import Felix.Laws as L
  hiding (Category; Cartesian; CartesianClosed) -- ; Logic

module Felix.Construct.Product
  {o₁} {obj₁ : Set o₁} {ℓ₁} {_⇨₁_ : obj₁ → obj₁ → Set ℓ₁} ⦃ _ : Category _⇨₁_ ⦄
  {o₂} {obj₂ : Set o₂} {ℓ₂} {_⇨₂_ : obj₂ → obj₂ → Set ℓ₂} ⦃ _ : Category _⇨₂_ ⦄
 where

open import Level using (_⊔_)
open import Data.Product using (_,_; proj₁; proj₂) renaming (_×_ to _×̇_)

Obj : Set (o₁ ⊔ o₂)
Obj = obj₁ ×̇ obj₂

infix 0 _⇨_
_⇨_ : Obj → Obj → Set (ℓ₁ ⊔ ℓ₂)
(a₁ , a₂) ⇨ (b₁ , b₂) = (a₁ ⇨₁ b₁) ×̇ (a₂ ⇨₂ b₂)

module product-instances where instance

  category : Category _⇨_
  category = record { id = id , id ; _∘_ = λ (g₁ , g₂) (f₁ , f₂) → (g₁ ∘ f₁) , (g₂ ∘ f₂) }

  products : ⦃ _ : Products obj₁ ⦄ ⦃ _ : Products obj₂ ⦄ → Products Obj
  products = record { ⊤ = ⊤ , ⊤ ; _×_ = λ (a₁ , a₂) (b₁ , b₂) → (a₁ × b₁) , (a₂ × b₂) }

  cartesian : ⦃ _ : Products  obj₁ ⦄ ⦃ _ : Products  obj₂ ⦄
              ⦃ _ : Cartesian _⇨₁_ ⦄ ⦃ _ : Cartesian _⇨₂_ ⦄
            → Cartesian _⇨_
  cartesian = record
    {  !  = ! , !
    ; _▵_ = λ (f₁ , f₂) (g₁ , g₂) → f₁ ▵ g₁ , f₂ ▵ g₂
    ; exl = exl , exl
    ; exr = exr , exr
    }

  traced : ⦃ _ : Products  obj₁ ⦄ ⦃ _ : Products  obj₂ ⦄
           ⦃ _ : Traced _⇨₁_ ⦄ ⦃ _ : Traced _⇨₂_ ⦄ →
           Traced _⇨_
  traced = record
    { WF = λ (f₁ , f₂) → WF f₁ ×̇ WF f₂
    ; trace = λ { (f₁ , f₂) (wf₁ , wf₂) → trace f₁ wf₁ , trace f₂ wf₂ }
    }


  -- boolean : ⦃ _ : Boolean obj₁ ⦄ ⦃ _ : Boolean obj₂ ⦄ → Boolean Obj
  -- boolean = record { Bool = Bool , Bool }

  -- logic : ⦃ _ : Products obj₁ ⦄ ⦃ _ : Products obj₂ ⦄
  --         ⦃ _ : Boolean  obj₁ ⦄ ⦃ _ : Boolean  obj₂ ⦄
  --         ⦃ _ : Logic    _⇨₁_ ⦄ ⦃ _ : Logic    _⇨₂_ ⦄
  --       → Logic _⇨_
  -- logic = record
  --           { false = false , false
  --           ; true  = true  , true
  --           ; not   =  not  ,  not
  --           ; ∧     =   ∧   ,   ∧
  --           ; ∨     =   ∨   ,   ∨
  --           ; xor   =  xor  ,  xor
  --           ; cond  = cond  , cond
  --           }

  equivalent : ∀ {q₁} ⦃ _ : Equivalent q₁ _⇨₁_ ⦄ {q₂} ⦃ _ : Equivalent q₂ _⇨₂_ ⦄
             → Equivalent (q₁ ⊔ q₂) _⇨_
  equivalent = record
    { _≈_ = λ (f₁ , f₂) (g₁ , g₂) → f₁ ≈ g₁ ×̇ f₂ ≈ g₂  -- Does this construction already exist?
    ; equiv = record
       { refl  = refl , refl
       ; sym   = λ (eq₁ , eq₂) → sym eq₁ , sym eq₂
       ; trans = λ (eq₁ , eq₂) (eq₁′ , eq₂′)  → trans eq₁ eq₁′ , trans eq₂ eq₂′
       }
    }

  l-category : ∀ {q₁} ⦃ _ : Equivalent q₁ _⇨₁_ ⦄ {q₂} ⦃ _ : Equivalent q₂ _⇨₂_ ⦄
               ⦃ _ : L.Category _⇨₁_ ⦄ ⦃ _ : L.Category _⇨₂_ ⦄
             → L.Category _⇨_
  l-category = record
    { identityˡ = identityˡ , identityˡ
    ; identityʳ = identityʳ , identityʳ
    ; assoc     =   assoc   ,   assoc
    ; ∘≈        = λ (eq₁ , eq₂) (eq₁′ , eq₂′) → ∘≈ eq₁ eq₁′ , ∘≈ eq₂ eq₂′
    }

  open import Function.Equivalence using (Equivalence; equivalence)
  open import Function.Equality as F using (Π; _⟨$⟩_)

  l-cartesian : ∀ {q₁} ⦃ _ : Equivalent q₁ _⇨₁_ ⦄ {q₂} ⦃ _ : Equivalent q₂ _⇨₂_ ⦄
                ⦃ _ :   Products  obj₁ ⦄ ⦃ _ :   Products  obj₂ ⦄
                ⦃ _ :   Cartesian _⇨₁_ ⦄ ⦃ _ :   Cartesian _⇨₂_ ⦄
                ⦃ _ : L.Category  _⇨₁_ ⦄ ⦃ _ : L.Category  _⇨₂_ ⦄
                ⦃ _ : L.Cartesian _⇨₁_ ⦄ ⦃ _ : L.Cartesian _⇨₂_ ⦄
             → L.Cartesian _⇨_
  l-cartesian = record
    { ∀⊤ = ∀⊤ , ∀⊤
    ; ∀× = λ { {a = a₁ , a₂} {b₁ , b₂} {c₁ , c₂} {f₁ , f₂} {g₁ , g₂} {k₁ , k₂} →
        let e₁ = ∀× {f = f₁} {g₁} {k₁}
            e₂ = ∀× {f = f₂} {g₂} {k₂}
            module Q₁ = Equivalence e₁
            module Q₂ = Equivalence e₂
            h₁ = Q₁.to ⟨$⟩_ ; h₁⁻¹ = Q₁.from ⟨$⟩_
            h₂ = Q₂.to ⟨$⟩_ ; h₂⁻¹ = Q₂.from ⟨$⟩_
        in
        equivalence
          (λ (z₁ , z₂) → let eq₁ , eq₁′ = h₁ z₁ ; eq₂ , eq₂′ = h₂ z₂ in
            (eq₁ , eq₂) , (eq₁′ , eq₂′)
            )
          (λ ((eq₁ , eq₂) , (eq₁′ , eq₂′)) →
            h₁⁻¹ (eq₁ , eq₁′) , h₂⁻¹ (eq₂ , eq₂′))
      }
    ; ▵≈ = λ { {f = f₁ , f₂} {g₁ , g₂} {h₁ , h₂} {k₁ , k₂}
               (h₁≈k₁ , h₂≈k₂) (f₁≈g₁ , f₂≈g₂) →
                 (▵≈ h₁≈k₁ f₁≈g₁) , ▵≈ h₂≈k₂ f₂≈g₂ }
    }

  -- l-logic : ∀ {q₁} ⦃ _ : Equivalent q₁ _⇨₁_ ⦄ {q₂} ⦃ _ : Equivalent q₂ _⇨₂_ ⦄
  --           ⦃ _ : Products  obj₁ ⦄ ⦃ _ : Products  obj₂ ⦄
  --           ⦃ _ : Boolean   obj₁ ⦄ ⦃ _ : Boolean   obj₂ ⦄
  --           ⦃ _ : Cartesian _⇨₁_ ⦄ ⦃ _ : Cartesian _⇨₂_ ⦄
  --           ⦃ _ :    Logic  _⇨₁_ ⦄ ⦃ _ :    Logic  _⇨₂_ ⦄
  --           ⦃ _ :  L.Logic  _⇨₁_ ⦄ ⦃ _ :  L.Logic  _⇨₂_ ⦄
  --         → L.Logic _⇨_
  -- l-logic = record { f∘cond = f∘cond , f∘cond }

module product-homomorphisms where instance

  Hₒ₁ : Homomorphismₒ Obj obj₁
  Hₒ₁ = record { Fₒ = proj₁ }

  H₁ : Homomorphism _⇨_ _⇨₁_
  H₁ = record { Fₘ = proj₁ }

  Hₒ₂ : Homomorphismₒ Obj obj₂
  Hₒ₂ = record { Fₒ = proj₂ }

  H₂ : Homomorphism _⇨_ _⇨₂_
  H₂ = record { Fₘ = proj₂ }

  catH₁ : ∀ {q₁ q₂} ⦃ _ : Equivalent q₁ _⇨₁_ ⦄ ⦃ _ : Equivalent q₂ _⇨₂_ ⦄ → CategoryH _⇨_ _⇨₁_
  catH₁ = record { F-cong = proj₁ ; F-id = refl ; F-∘ = refl }

  catH₂ : ∀ {q₁ q₂} ⦃ _ : Equivalent q₁ _⇨₁_ ⦄ ⦃ _ : Equivalent q₂ _⇨₂_ ⦄ → CategoryH _⇨_ _⇨₂_
  catH₂ = record { F-cong = proj₂ ; F-id = refl ; F-∘ = refl }

  pH₁ : ∀ ⦃ _ : Products obj₁ ⦄ ⦃ _ : Products obj₂ ⦄ → ProductsH Obj _⇨₁_
  pH₁ = record { ε = id ; μ = id ; ε⁻¹ = id ; μ⁻¹ = id }

  spH₁ : ∀ {q₁} ⦃ _ : Equivalent q₁ _⇨₁_ ⦄
    ⦃ _ : Products obj₁ ⦄ ⦃ _ : Products obj₂ ⦄
    ⦃ _ : L.Category _⇨₁_ ⦄
    → StrongProductsH Obj _⇨₁_
  spH₁ = record { ε⁻¹∘ε = identityˡ
                ; ε∘ε⁻¹ = identityˡ
                ; μ⁻¹∘μ = identityˡ
                ; μ∘μ⁻¹ = identityˡ }

  pH₂ : ∀ ⦃ _ : Products obj₁ ⦄ ⦃ _ : Products obj₂ ⦄ → ProductsH Obj _⇨₂_
  pH₂ = record { ε = id ; μ = id ; ε⁻¹ = id ; μ⁻¹ = id}

  spH₂ : ∀ {q₂} ⦃ _ : Equivalent q₂ _⇨₂_ ⦄
    ⦃ _ : Products obj₁ ⦄ ⦃ _ : Products obj₂ ⦄
    ⦃ _ : L.Category _⇨₂_ ⦄
    → StrongProductsH Obj _⇨₂_
  spH₂ = record { ε⁻¹∘ε = identityˡ
                ; ε∘ε⁻¹ = identityˡ
                ; μ⁻¹∘μ = identityˡ
                ; μ∘μ⁻¹ = identityˡ }

  cartesianH₁ : ∀ {q₁ q₂} ⦃ _ : Equivalent q₁ _⇨₁_ ⦄ ⦃ _ : Equivalent q₂ _⇨₂_ ⦄
      ⦃ _ : Products  obj₁ ⦄ ⦃ _ : Products  obj₂ ⦄
      ⦃ _ : Cartesian _⇨₁_ ⦄ ⦃ _ : Cartesian _⇨₂_ ⦄ ⦃ _ : L.Category _⇨₁_ ⦄
    → CartesianH _⇨_ _⇨₁_
  cartesianH₁ = record
    { F-!   = sym identityˡ
    ; F-▵   = sym identityˡ
    ; F-exl = identityʳ
    ; F-exr = identityʳ }

  cartesianH₂ : ∀ {q₁ q₂} ⦃ _ : Equivalent q₁ _⇨₁_ ⦄ ⦃ _ : Equivalent q₂ _⇨₂_ ⦄
      ⦃ _ : Products  obj₁ ⦄ ⦃ _ : Products  obj₂ ⦄
      ⦃ _ : Cartesian _⇨₁_ ⦄ ⦃ _ : Cartesian _⇨₂_ ⦄ ⦃ _ : L.Category _⇨₂_ ⦄
    → CartesianH _⇨_ _⇨₂_
  cartesianH₂ = record
    { F-!   = sym identityˡ
    ; F-▵   = sym identityˡ
    ; F-exl = identityʳ
    ; F-exr = identityʳ }

--   booleanH₁ :
--       ∀ {q₁} ⦃ _ : Equivalent q₁ _⇨₁_ ⦄ ⦃ _ : Boolean obj₁ ⦄ ⦃ _ : Boolean obj₂ ⦄
--       ⦃ _ : L.Category _⇨₁_ ⦄
--     → BooleanH Obj _⇨₁_
--   booleanH₁ = record { β = id ; β⁻¹ = id }

--   booleanH₂ :
--       ∀ {q₂} ⦃ _ : Equivalent q₂ _⇨₂_ ⦄ ⦃ _ : Boolean obj₁ ⦄ ⦃ _ : Boolean obj₂ ⦄
--       ⦃ _ : L.Category _⇨₂_ ⦄
--     → BooleanH Obj _⇨₂_
--   booleanH₂ = record { β = id ; β⁻¹ = id }

--   strongBooleanH₁ : 
--       ∀ {q₁} ⦃ _ : Equivalent q₁ _⇨₁_ ⦄ ⦃ _ : Boolean obj₁ ⦄ ⦃ _ : Boolean obj₂ ⦄
--       ⦃ _ : L.Category _⇨₁_ ⦄
--     → StrongBooleanH Obj _⇨₁_
--   strongBooleanH₁ = record { β⁻¹∘β = identityˡ ; β∘β⁻¹ = identityˡ }

--   open import Felix.Reasoning

--   logicH₁ : ∀ {q₁} ⦃ _ : Equivalent q₁ _⇨₁_ ⦄
--       ⦃ _ : Products   obj₁ ⦄ ⦃ _ : Products   obj₂ ⦄
--       ⦃ _ : Boolean    obj₁ ⦄ ⦃ _ : Boolean    obj₂ ⦄
--       ⦃ _ : Logic      _⇨₁_ ⦄ ⦃ _ : Logic      _⇨₂_ ⦄
--       ⦃ _ : Cartesian  _⇨₁_ ⦄ ⦃ _ : L.Category _⇨₁_ ⦄ ⦃ _ : L.Cartesian _⇨₁_ ⦄
--     → LogicH _⇨_ _⇨₁_
--   logicH₁ = record
--               { F-false =      identityʳ      ; sym identityˡ
--               ; F-true  =      identityʳ      ; sym identityˡ
--               ; F-not   =      identityʳ      ; sym identityˡ
--               ; F-∧     = elimʳ (elimʳ id⊗id) ; sym identityˡ
--               ; F-∨     = elimʳ (elimʳ id⊗id) ; sym identityˡ
--               ; F-xor   = elimʳ (elimʳ id⊗id) ; sym identityˡ
--               ; F-cond  = elimʳ (elimʳ id⊗id)
--               }


--   logicH₂ : ∀ {q₂} ⦃ _ : Equivalent q₂ _⇨₂_ ⦄
--       ⦃ _ : Products   obj₁ ⦄ ⦃ _ : Products   obj₂ ⦄
--       ⦃ _ : Boolean    obj₁ ⦄ ⦃ _ : Boolean    obj₂ ⦄
--       ⦃ _ : Logic      _⇨₁_ ⦄ ⦃ _ : Logic      _⇨₂_ ⦄
--       ⦃ _ : Cartesian  _⇨₂_ ⦄ ⦃ _ : L.Category _⇨₂_ ⦄ ⦃ _ : L.Cartesian _⇨₂_ ⦄
--     → LogicH _⇨_ _⇨₂_
--   logicH₂ = record
--               { F-false =      identityʳ      ; sym identityˡ
--               ; F-true  =      identityʳ      ; sym identityˡ
--               ; F-not   =      identityʳ      ; sym identityˡ
--               ; F-∧     = elimʳ (elimʳ id⊗id) ; sym identityˡ
--               ; F-∨     = elimʳ (elimʳ id⊗id) ; sym identityˡ
--               ; F-xor   = elimʳ (elimʳ id⊗id) ; sym identityˡ
--               ; F-cond  = elimʳ (elimʳ id⊗id)
--               }

-- -- TODO: Factor out some of the instance requirements as submodule arguments.
