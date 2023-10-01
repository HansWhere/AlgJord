module Control.Function.PointFree where
open import Agda.Primitive using (Level)

private 
    variable
        ℓA ℓB ℓC : Level 
        A : Set ℓA
        B : Set ℓB
        C : Set ℓC


S : (A → B → C) → (A → B) → (A → C)
S f g a = (f a) (g a)

K : A → B → A
K a b = a

I : A → A
I a = a
