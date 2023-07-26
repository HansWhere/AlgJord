module Num.Integer.PositiveAndNegsuc.Definition where
open import Num.Natural.Definition using (ℕ; succ; zero) public
-- open import Relation.Equality as ≡ using (_≡_; _≡⟨_⟩_; _≡⟨'_⟩_; _≡⟨⟩_; _∎; _◈_)

data ℤ : Set where
    pos : ℕ → ℤ
    nsc : ℕ → ℤ
{-# BUILTIN INTEGER ℤ #-}
{-# BUILTIN INTEGERPOS pos #-}
{-# BUILTIN INTEGERNEGSUC nsc #-}

neg : ℕ → ℤ
neg zero = pos zero 
neg (succ x) = nsc x 

infixl 60 _−_ 
_−_ : ℕ → ℕ → ℤ
x − zero = pos x  
zero − succ y = nsc y 
succ x − succ y = x − y
