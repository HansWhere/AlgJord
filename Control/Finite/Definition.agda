module Control.Finite.Definition where 
open import Num.Natural.Definition as ℕ using (ℕ)

data Fin : ℕ → Set where 
    zero : {n : ℕ} → Fin n
    succ : {n : ℕ} → Fin n → Fin (ℕ.succ n) 