module Logic.Connective where
open import Agda.Primitive using (Level; _⊔_)
open import Logic.Absurdum public

private 
    variable
        ℓA ℓB ℓC : Level
        A : Set ℓA
        B : Set ℓB
        C : Set ℓC

infixl 15 _∧_
infixl 10 _∨_
infixl 10 _,_ _but_

record _∧_ (A : Set ℓA) (B : Set ℓB) : Set (ℓA ⊔ ℓB) where 
    constructor _,_ 
    field
        fst : A 
        snd : B 
open _∧_ public

data _∨_ (A : Set ℓA) (B : Set ℓB) : Set (ℓA ⊔ ℓB) where
    lft : A → A ∨ B
    rgt : B → A ∨ B 

_but_ : A ∨ B → ¬ B → A
lft a but ¬b = a
rgt b but ¬b = ecq (¬b b) 

module ∧ where
    comm : A ∧ B → B ∧ A
    comm (a , b) = b , a

    assoc : A ∧ B ∧ C → A ∧ (B ∧ C)
    assoc (a , b , c) = a , (b , c)

    idenL : ⊤ ∧ A → A
    idenL (tt , a) = a

    idenR : A ∧ ⊤ → A
    idenR (a , tt) = a

    zeroL : ⊥ ∧ A → ⊥
    zeroL ()

    zeroR : A ∧ ⊥ → ⊥
    zeroR ()

    -- deM : ¬ (A ∧ B) → ¬ A ∨ ¬ B

    deM' : ¬ A ∨ ¬ B → ¬ (A ∧ B)
    deM' (lft ¬a) (a , b) = ¬a a
    deM' (rgt ¬b) (a , b) = ¬b b 

    module over∨ where
        distrL : A ∧ (B ∨ C) → (A ∧ B) ∨ (A ∧ C)
        distrL (a , lft b) = lft (a , b)
        distrL (a , rgt c) = rgt (a , c)

        distrR : (A ∨ B) ∧ C → (A ∧ C) ∨ (B ∧ C)
        distrR (lft a , c) = lft (a , c)
        distrR (rgt b , c) = rgt (b , c) 

module ∨ where
    elim : A ∨ B → (A → C) → (B → C) → C
    elim (lft a) f _ = f a
    elim (rgt b) _ g = g b

    comm : A ∨ B → B ∨ A
    comm (lft a) = rgt a
    comm (rgt b) = lft b

    assoc : A ∨ B ∨ C → A ∨ (B ∨ C)
    assoc (lft (lft a)) = lft a
    assoc (lft (rgt b)) = rgt (lft b)
    assoc (rgt c) = rgt (rgt c)

    idenL : ⊥ ∨ A → A
    idenL (lft boom) = ecq boom
    idenL (rgt a) = a

    idenR : A ∨ ⊥ → A
    idenR (lft a) = a
    idenR (rgt boom) = ecq boom

    zeroL : ⊤ ∨ A → ⊤
    zeroL _ = tt

    zeroR : A ∨ ⊤ → ⊤
    zeroR _ = tt

    deM : ¬ (A ∨ B) → ¬ A ∧ ¬ B
    deM ¬a∨b = (λ a → ¬a∨b (lft a)) , (λ b → ¬a∨b (rgt b)) 
    
    deM' : ¬ A ∧ ¬ B → ¬ (A ∨ B)
    deM' (¬a , ¬b) (lft a) = ¬a a
    deM' (¬a , ¬b) (rgt b) = ¬b b

    module over∨ where
        distrL : A ∨ (B ∧ C) → (A ∨ B) ∧ (A ∨ C)
        distrL (lft a) = lft a , lft a
        distrL (rgt (b , c)) = rgt b , rgt c 

        distrR : (A ∨ B) ∧ C → (A ∨ C) ∧ (B ∨ C)
        distrR (lft a , c) = (lft a , rgt c)
        distrR (rgt b , c) = (rgt c , lft b)