{-# OPTIONS --copatterns #-}
module Num.Integer.SubtractionClosure.Definition where
open import Num.Natural.Definition using (ℕ; succ; zero) public
open import Num.Natural.Algebra
open + using (_+_) public
open import Relation.Equality as ≡ using (_≡_; _≡⟨_⟩_; _≡⟨'_⟩_; _≡⟨⟩_; _∎; _◈_; _➤_)
open import Relation.Equivalance public

infixl 60 _−_
infix 40 _≃_

data ℤ : Set where
    _−_ : ℕ → ℕ → ℤ

_≃_ : ℤ → ℤ → Set
x₁ − x₂ ≃ y₁ − y₂ = x₁ + y₂ ≡ x₂ + y₁

instance
    ≃-Trans : Trans _≃_
    Trans.trans ≃-Trans {x₁ − x₂} {y₁ − y₂} {z₁ − z₂} x≃y y≃z = 
        +.canc (x₁ + z₂) (x₂ + z₁) (y₁ + y₂) (
                x₁ + z₂ + (y₁ + y₂)
            ≡⟨ (λ u → x₁ + z₂ + u) ◈ +.comm y₁ y₂ ⟩
                x₁ + z₂ + (y₂ + y₁)
            ≡⟨ +.assoc x₁ z₂ (y₂ + y₁) ⟩
                x₁ + (z₂ + (y₂ + y₁))
            ≡⟨ (λ u → x₁ + u) ◈ +.comm z₂ (y₂ + y₁) ⟩
                x₁ + ((y₂ + y₁) + z₂)
            ≡⟨ (λ u → x₁ + u) ◈ +.assoc y₂ y₁ z₂ ⟩
                x₁ + (y₂ + (y₁ + z₂))
            ≡⟨' +.assoc x₁ y₂ (y₁ + z₂) ⟩
                x₁ + y₂ + (y₁ + z₂)
            ≡⟨ ≡.cong2 _+_ x≃y y≃z ⟩
                x₂ + y₁ + (y₂ + z₁)
            ≡⟨ +.assoc x₂ y₁ (y₂ + z₁) ⟩
                x₂ + (y₁ + (y₂ + z₁))
            ≡⟨' (λ u → x₂ + u) ◈ +.assoc y₁ y₂ z₁ ⟩
                x₂ + ((y₁ + y₂) + z₁)
            ≡⟨ (λ u → x₂ + u) ◈ +.comm (y₁ + y₂) z₁ ⟩
                x₂ + (z₁ + (y₁ + y₂))
            ≡⟨' +.assoc x₂ z₁ (y₁ + y₂) ⟩
                x₂ + z₁ + (y₁ + y₂)
            ∎
        )
        
    ≃-Symm : Symm _≃_
    Symm.symm ≃-Symm {x₁ − x₂} {y₁ − y₂} x≃y = +.comm y₁ x₂ ➤ ≡.symm x≃y ➤ +.comm x₁ y₂

    ≃-Refl : Refl _≃_
    Refl.refl ≃-Refl {x₁ − x₂} = +.comm x₁ x₂

    ≃-Eqv : Eqv _≃_
    ≃-Eqv = record
        {   -Trans = ≃-Trans
        ;   -Symm = ≃-Symm
        ;   -Refl = ≃-Refl
        }