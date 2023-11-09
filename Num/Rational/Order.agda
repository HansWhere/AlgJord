module Num.Rational.Order where
open import Control.Function.Util hiding (id)
open import Num.Rational.Definition as ℚ: using (ℚ; _÷_asℚ_; _≇_; _≅_) 
open import Num.Rational.Algebra as ℚ
open import Num.Integer.Definition as ℤ: using (ℤ)
open import Num.Integer.Algebra as ℤ using () renaming (_*_ to _∙_)
open import Num.Integer.Order as ℤ≤ using () renaming (_≤_ to _ℤ≤_)
open import Logic.Quantifier public
open import Logic.Connective public

_≤_ : ℚ → ℚ → Set
p ÷ q asℚ q≠0 ≤ r ÷ s asℚ s≠0 = p ∙ s ℤ≤ q ∙ r

_<_ : ℚ → ℚ → Set
x < y = x ≤ y ∧ x ≇ y