module Control.List.Vector.Definition where
open import Agda.Primitive using (Level)
open import Num.Natural.Definition using (ℕ)
import Control.List.Definition

private 
    variable
        ℓ ℓ' : Level

infixr 50 _:,_
data Vec (A : Set ℓ) : ℕ → Set ℓ where 
    ⟨⟩ : Vec A 0
    _:,_ : {n : ℕ} → A → Vec A n → Vec A (ℕ.succ n)