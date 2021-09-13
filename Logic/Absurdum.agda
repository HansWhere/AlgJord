module Logic.Absurdum where
open import Agda.Primitive using (Level)
private 
    variable 
        ℓ : Level 

infixr 30 ¬_

data ⊥ : Set where

¬_ : Set → Set
¬ A = A → ⊥