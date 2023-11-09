module Num.Integer.Definition where
open import Control.Function.Util hiding (id)
open import Logic.Quantifier public
open import Logic.Connective public
open import Num.Natural.Definition using (ℕ; succ; zero)
open import Num.Natural.Algebra as ℕ
open import Relation.Equivalance as ≃ hiding (trans; symm; refl)
open import Relation.Equality as ≡ using (_≡_; _≡⟨_⟩_; _≡⟨'_⟩_; _≡⟨⟩_; _∎; _◈_; _≡➤_; _≡➤`_)

infix 60 _−_ 
infix 40 _≅_

data ℤ : Set where
    _−_ : ℕ → ℕ → ℤ

_≅_ : ℤ → ℤ → Set
x1 − x2 ≅ y₁ − y₂ = x1 + y₂ ≡ x2 + y₁

_≇_ : ℤ → ℤ → Set
x ≇ y = ¬ x ≅ y

0z : ℤ
0z = 0 − 0

1z : ℤ
1z = 1 − 0

ℤ+ : ℕ → ℤ
ℤ+ n = n − 0

ℤ− : ℕ → ℤ
ℤ− n = 0 − n

module ≅ where
    trans : {x y z : ℤ} → x ≅ y → y ≅ z → x ≅ z
    trans {x1 − x2} {y₁ − y₂} {z₁ − z₂} x≅y y≅z = 
        +.canc (x1 + z₂) (x2 + z₁) (y₁ + y₂) (
                x1 + z₂ + (y₁ + y₂)
            ≡⟨ (λ u → x1 + z₂ + u) ◈ +.comm y₁ y₂ ⟩
                x1 + z₂ + (y₂ + y₁)
            ≡⟨ +.assoc x1 z₂ (y₂ + y₁) ⟩
                x1 + (z₂ + (y₂ + y₁))
            ≡⟨ (λ u → x1 + u) ◈ +.comm z₂ (y₂ + y₁) ⟩
                x1 + ((y₂ + y₁) + z₂)
            ≡⟨ (λ u → x1 + u) ◈ +.assoc y₂ y₁ z₂ ⟩
                x1 + (y₂ + (y₁ + z₂))
            ≡⟨' +.assoc x1 y₂ (y₁ + z₂) ⟩
                x1 + y₂ + (y₁ + z₂)
            ≡⟨ ≡.cong2 _+_ x≅y y≅z ⟩
                x2 + y₁ + (y₂ + z₁)
            ≡⟨ +.assoc x2 y₁ (y₂ + z₁) ⟩
                x2 + (y₁ + (y₂ + z₁))
            ≡⟨' (λ u → x2 + u) ◈ +.assoc y₁ y₂ z₁ ⟩
                x2 + ((y₁ + y₂) + z₁)
            ≡⟨ (λ u → x2 + u) ◈ +.comm (y₁ + y₂) z₁ ⟩
                x2 + (z₁ + (y₁ + y₂))
            ≡⟨' +.assoc x2 z₁ (y₁ + y₂) ⟩
                x2 + z₁ + (y₁ + y₂)
            ∎
        )

    symm : {x y : ℤ} → x ≅ y → y ≅ x
    symm {x1 − x2} {y₁ − y₂} x≅y = +.comm y₁ x2 ≡➤ ≡.symm x≅y ≡➤ +.comm x1 y₂

    refl : {x : ℤ} → x ≅ x
    refl {x1 − x2} = +.comm x1 x2

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

abs : ℤ → ℤ
abs x@(x1 − x2) with trichotomy x
... | rgt _ = x
... | lft (rgt _) = x2 − x1
... | lft (lft _) = x

decidable-0 : (x : ℤ) → x ≅ 0 − 0 ∨ ¬ x ≅ 0 − 0
decidable-0 (0 − 0) = lft ≡.refl
decidable-0 (succ x − 0) = rgt λ()
decidable-0 (0 − succ y) = rgt λ()
decidable-0 (succ x − succ y) with decidable-0 (x − y)
... | lft (is0) = lft (succ ◈ is0)
... | rgt (isnt0) = rgt (λ eq → isnt0 (ℕ.+.pred ◈ eq))