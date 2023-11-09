module Num.Rational.Algebra where
open import Control.Function.Util hiding (id)
open import Num.Rational.Definition as ℚ:
open import Num.Integer.Definition as ℤ:
open import Num.Integer.Algebra as ℤ using () renaming (_+_ to _⊹_; _*_ to _×_)
import Num.Natural.Algebra as ℕ
open import Num.Natural.Definition using (ℕ; 1≠0)
open import Relation.Equality as ≡ using (_≡_; _≡⟨_⟩_; _≡⟨'_⟩_; _≡⟨⟩_; _∎; _◈_; _≡➤_)
open import Relation.Equivalance as ≃

module + where
    infixl 60 _+_ 

    _+_ : ℚ → ℚ → ℚ
    p ÷ q asℚ q≠0 + r ÷ s asℚ s≠0 = (p × s ⊹ q × r) ÷ q × s asℚ λ q*s≠0 → q≠0 (ℤ.*.no-0divisor q s q*s≠0 s≠0)

    neg : ℚ → ℚ
    neg ((p1 ℤ.− p2) ÷ q asℚ q≠0) = (p2 ℤ.− p1) ÷ q asℚ q≠0

    _-_ : ℚ → ℚ → ℚ
    x - y = x + neg y