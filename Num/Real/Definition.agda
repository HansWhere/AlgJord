module Num.Real.Definition where
open import Relation.Equality as ≡ using (_≡_; _≡⟨_⟩_; _≡⟨'_⟩_; _≡⟨⟩_; _∎; _◈_; _≡➤_; _≡➤`_)
open import Num.Natural.Definition as ℕ: using (ℕ; succ) 
open import Num.Integer.Definition as ℤ: using (ℤ; _−_; 1z; 0z)
open import Num.Rational.Definition as ℚ: using (ℚ; _÷_asℚ_; 1q; 0q) 
import Num.Natural.Algebra as ℕ 
import Num.Integer.Algebra as ℤ
import Num.Rational.Algebra as ℚ
open ℚ.+ using () renaming (_-_ to _ℚ-_)
open import Num.Rational.Order as ℚ≤ using () renaming (_≤_ to _ℚ≤_; _<_ to _ℚ<_)
open import Logic.Absurdum
open import Logic.Quantifier

data ℝ : Set where
    _asℝ_ : (seq : ℕ → ℚ) → ((n : ℕ) → ∃ ℕ λ M → (Δ1 Δ2 : ℕ) → ℚ:.abs (seq (M ℕ.+ Δ1) ℚ- seq (M ℕ.+ Δ2)) ℚ< (1z ÷ (succ n − 0) asℚ λ())) → ℝ

0r : ℝ
0r = (λ i → 0q) asℝ λ n → (0 :, λ Δ1 Δ2 → {!   !})