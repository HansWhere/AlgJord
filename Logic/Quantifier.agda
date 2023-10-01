module Logic.Quantifier where
open import Agda.Primitive using (Level; _⊔_)

private 
    variable
        ℓ ℓ' : Level

infix 10 _:,_
record ∃ (A : Set ℓ) (P : A → Set ℓ') : Set (ℓ ⊔ ℓ') where
    constructor _:,_
    field
        obj : A
        prop : P obj 
open ∃ public

{-# BUILTIN SIGMA ∃ #-}