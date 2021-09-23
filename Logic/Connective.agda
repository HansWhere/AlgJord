module Logic.Connective where
open import Agda.Primitive using (Level; _⊔_)

private 
    variable
        ℓ ℓ' : Level

infixl 20 _∧_
infixl 10 _∨_
infixl 10 _⹁_ 

record _∧_ (A : Set ℓ) (B : Set ℓ') : Set (ℓ ⊔ ℓ') where 
    constructor _⹁_ 
    field
        fst : A 
        snd : B 
open _∧_ public

data _∨_ (A : Set ℓ) (B : Set ℓ') : Set (ℓ ⊔ ℓ') where
    lft : A → A ∨ B
    rgt : B → A ∨ B 
