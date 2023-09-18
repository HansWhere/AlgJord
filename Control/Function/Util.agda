module Control.Function.Util where
open import Agda.Primitive using (Level)

private 
    variable
        ℓ ℓ' : Level 

infixl 0 _$_ 

_$_ : {A : Set ℓ} {B : Set ℓ'} → (A → B) → A → B
f $ x = f x

