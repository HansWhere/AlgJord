module Algebra.Operator.Binary.Permutation where
open import Agda.Primitive using (Level)
open import Control.List.Definition
open import Num.Natural.Definition as ℕ using (ℕ; succ; zero)
open import Control.Finite.Definition

private 
    variable
        ℓ : Level

-- perm : {n : ℕ} → List (List (Fin n))