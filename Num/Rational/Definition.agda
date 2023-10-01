module Num.Rational.Definition where
open import Relation.Equality as ≡
open import Relation.Equivalance as ≃
open import Num.Natural.Definition as ℕ
open import Num.Integer.Definition as ℤ using (ℤ; _−_)
open import Num.Integer.Algebra
open * using (_*_)
open import Logic.Absurdum

infix 55 _÷_asℚ_
infix 40 _≅_

data ℚ : Set where
    _÷_asℚ_ : (x y : ℤ) → (¬ y ℤ.≅ 0 − 0) → ℚ

_≅_ : ℚ → ℚ → Set
p ÷ q asℚ q≠0 ≅ r ÷ s asℚ s≠0 = p * s ≡ r * q

instance
    ≅-Trans : Trans _≅_
    Trans.trans ≅-Trans {p ÷ q asℚ q≠0} {r ÷ s asℚ s≠0} {u ÷ v asℚ u≠0} x≅y y≅z = {!   !}
        
    -- ≅-Symm : Symm _≅_
    -- Symm.symm ≅-Symm {x₁ − x₂} {y₁ − y₂} x≅y = +.comm y₁ x₂ ≡➤ ≡.symm x≅y ≡➤ +.comm x₁ y₂
    --     -- ≡.trans (+.comm y₁ x₂) (≡.trans (≡.symm x≅y) (+.comm x₁ y₂))

    -- ≅-Refl : Refl _≅_
    -- Refl.refl ≅-Refl {x₁ − x₂} = +.comm x₁ x₂

    -- ≅-Eqv : Eqv _≅_
    -- ≅-Eqv = record
    --     {   -Trans = ≅-Trans
    --     ;   -Symm = ≅-Symm
    --     ;   -Refl = ≅-Refl
    --     }

    -- ℤ-EqvSet : EqvSet ℤ
    -- EqvSet._≃_ ℤ-EqvSet = _≅_

private
    one : ℚ
    one = (1 − 0) ÷ (1 − 0) asℚ λ() 