{-# OPTIONS --copatterns #-}
module Num.Integer.Definition where
open import Control.Function.Util
open import Logic.Quantifier public
open import Logic.Connective public
open import Num.Natural.Definition using (ℕ; succ; zero)
open import Num.Natural.Algebra
open + using (_+_)
open import Relation.Equivalance as ≃ hiding (trans; symm; refl)
open import Relation.Equality as ≡ using (_≡_; _≡⟨_⟩_; _≡⟨'_⟩_; _≡⟨⟩_; _∎; _◈_; _≡➤_; _≡➤`_)

infix 60 _−_ 
infix 40 _≅_

data ℤ : Set where
    _−_ : ℕ → ℕ → ℤ

_≅_ : ℤ → ℤ → Set
x₁ − x₂ ≅ y₁ − y₂ = x₁ + y₂ ≡ x₂ + y₁

_≇_ : ℤ → ℤ → Set
x ≇ y = ¬ x ≅ y

0z : ℤ
0z = 0 − 0

ℤ+ : ℕ → ℤ
ℤ+ n = n − 0

ℤ− : ℕ → ℤ
ℤ− n = 0 − n

trans : {x y z : ℤ} → x ≅ y → y ≅ z → x ≅ z
trans {x₁ − x₂} {y₁ − y₂} {z₁ − z₂} x≅y y≅z = 
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
        ≡⟨ ≡.cong2 _+_ x≅y y≅z ⟩
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

symm : {x y : ℤ} → x ≅ y → y ≅ x
symm {x₁ − x₂} {y₁ − y₂} x≅y = +.comm y₁ x₂ ≡➤ ≡.symm x≅y ≡➤ +.comm x₁ y₂

refl : {x : ℤ} → x ≅ x
refl {x₁ − x₂} = +.comm x₁ x₂

instance
    ≅-Trans : Trans _≅_
    Trans.trans ≅-Trans = trans
        
    ≅-Symm : Symm _≅_
    Symm.symm ≅-Symm = symm

    ≅-Refl : Refl _≅_
    Refl.refl ≅-Refl = refl

    ≅-Eqv : Eqv _≅_
    ≅-Eqv = record
        {   -Trans = ≅-Trans
        ;   -Symm = ≅-Symm
        ;   -Refl = ≅-Refl
        }

    ℤ-EqvSet : EqvSet ℤ
    EqvSet._≃_ ℤ-EqvSet = _≅_

trichotomy : (x : ℤ) → (∃ ℕ λ n → x ≅ succ n − 0) ∨ (∃ ℕ λ n → x ≅ 0 − succ n) ∨ (x ≅ 0 − 0)
trichotomy (0 − 0) = rgt ≡.refl
trichotomy (succ x − 0) rewrite +.comm x 0 = lft $ lft $ x :, ≡.refl
trichotomy (0 − succ y) rewrite +.comm y 0 = lft $ rgt $ y :, ≡.refl
trichotomy (succ x − succ y) with trichotomy (x − y)
... |   rgt eq = rgt (succ ◈ eq)
... |   lft (lft (n :, x≡n+1)) = lft (lft (n :, succ ◈ (x≡n+1 ≡➤` +.left-succ y n)))
... |   lft (rgt (n :, y≡-n-1)) = lft (rgt (n :, succ ◈ (+.left-succ x n ≡➤ y≡-n-1)))
