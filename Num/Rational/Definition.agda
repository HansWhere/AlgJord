module Num.Rational.Definition where
open import Num.Integer.Definition as ℤ using (ℤ; _≅_) renaming (_−_ to _-−_)

data ℚ : Set where
    _/_ : ℤ 