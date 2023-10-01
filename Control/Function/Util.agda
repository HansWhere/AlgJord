module Control.Function.Util where
open import Agda.Primitive using (Level)

private 
    variable
        ℓA ℓB ℓC : Level 
        A : Set ℓA
        B : Set ℓB
        C : Set ℓC

infixr 0 _$_
infixl 0 _$'_
infixl 10 _<*>_ 
infixr 90 _∘_

_$_ : (A → B) → A → B
f $ a = f a

_$'_ : A → (A → B) → B
a $' f = f a

_∘_ : (B → C) → (A → B) → (A → C)
(f ∘ g) a = f $ g a

_<*>_ : (A → B → C) → (A → B) → (A → C)
(f <*> g) a = f a $ g a

flip : (A → B → C) → B → A → C
flip f b a = f a b

const : A → B → A
const a b = a 

id : A → A
id a = a
