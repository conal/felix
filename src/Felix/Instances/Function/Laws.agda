{-# OPTIONS --safe --without-K #-}

open import Level

module Felix.Instances.Function.Laws (ℓ : Level) where

open import Function using (mk⇔)
open import Data.Product using (_,_)
open import Data.Sum using (inj₁; inj₂)

open import Felix.Raw hiding (Category; Cartesian; Distributive; CartesianClosed)
open import Felix.Laws
open import Felix.Equiv
open import Felix.Instances.Function.Raw ℓ public
open import Axiom.Extensionality.Propositional
open import Relation.Binary.PropositionalEquality
     renaming ( refl to refl≡
              ; trans to trans≡
              ; sym to sym≡
              )

module →-laws-instances where

  instance

    category : Category _⇾_
    category = record
      { identityˡ = λ _ → refl≡
      ; identityʳ = λ _ → refl≡
      ; assoc     = λ _ → refl≡
      ; ∘≈        = λ { {f = f}{k = k} h≈k f≈g x →
                      trans≡ (h≈k (f x)) (cong k (f≈g x)) }
      }

    cartesian : Cartesian _⇾_
    cartesian = record
      { ∀⊤ = λ _ → refl≡
      ; ∀× = mk⇔
          (λ k≈f▵g → (λ x → cong exl (k≈f▵g x)) , (λ x → cong exr (k≈f▵g x)))
          (λ (exl∘k≈f , exr∘k≈g) x → cong₂ _,_ (exl∘k≈f x) (exr∘k≈g x))
      ; ▵≈ = λ h≈k f≈g x → cong₂ _,_ (h≈k x) (f≈g x)
      }

    distributive : Distributive _⇾_
    distributive = record
      { distribˡ∘distribˡ⁻¹ = λ where
        (_ , inj₁ _) → refl≡
        (_ , inj₂ _) → refl≡
      ; distribˡ⁻¹∘distribˡ = λ where
        (inj₁ _) → refl≡
        (inj₂ _) → refl≡
      ; distribʳ∘distribʳ⁻¹ = λ where
        (inj₁ _ , _) → refl≡
        (inj₂ _ , _) → refl≡
      ; distribʳ⁻¹∘distribʳ = λ where
        (inj₁ _) → refl≡
        (inj₂ _) → refl≡
      }

    module ccc (extensionality : Extensionality _ _) where

      cartesianClosed : CartesianClosed _⇾_
      cartesianClosed = record
        { ∀⇛ = mk⇔
            (λ g≈f (x , y) → sym≡ (cong (λ h → h y) (g≈f x)))
            (λ f≈uncurry-g x → extensionality λ y → sym≡ (f≈uncurry-g (x , y)))
        ; curry≈ = λ f≈g x → extensionality λ y → f≈g (x , y)
        }
