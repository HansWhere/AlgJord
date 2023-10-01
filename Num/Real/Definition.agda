module Num.Real.Definition where
open import Relation.Equality as ≡
open import Num.Natural.Definition as ℕ
open import Num.Integer.Definition as ℤ using (ℤ; _≅_) renaming (_−_ to _-−_)
open import Num.Rational.Definition as ℚ using (ℚ) 
open import Logic.Absurdum
open import Logic.Quantifier

data ℝ : Set where
    _asℝ_ : (seq : ℕ → ℚ) → ({ε : ℚ} → ∃ ℕ λ N → {n : ℕ} → 0 ≡ 0) → ℝ

private
    one : ℝ
    one = _