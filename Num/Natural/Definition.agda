module Num.Natural.Definition where
open import Relation.Equality as ≡ using (_≡_; _≡⟨_⟩_; _≡⟨'_⟩_; _≡⟨⟩_; _∎; _◈_)
open import Logic.Connective

data ℕ : Set where
    zero : ℕ
    succ : ℕ → ℕ
{-# BUILTIN NATURAL ℕ #-}
