module Logic.Absurdum where
open import Agda.Primitive using (Level)
private 
    variable 
        ℓ : Level 

infixr 30 ¬_

data ⊥ : Set where

data ⊤ : Set where
    tt : ⊤

¬_ : Set ℓ → Set ℓ
¬ A = A → ⊥

ecq : {A : Set ℓ} → ⊥ → A
ecq ()

contrapos : {A B : Set} → (A → B) → ¬ B → ¬ A
contrapos p ¬b a = ¬b (p a)