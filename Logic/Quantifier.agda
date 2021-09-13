module Logic.Quantifier where
open import Agda.Primitive using (Level; _⊔_)

private 
    variable
        ℓ ℓ' : Level

record ∃ (A : Set ℓ) (P : A → Set ℓ') : Set (ℓ ⊔ ℓ') where
    constructor _s,t,_
    field
        obj : A
        prop : P obj 

{-# BUILTIN SIGMA ∃ #-}