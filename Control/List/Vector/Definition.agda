module Control.List.Vector.Definition where
open import Agda.Primitive using (Level)
open import Relation.Equality
open import Num.Natural.Definition using (ℕ)
open import Num.Natural.Algebra
open + using (_+_)
import Control.List.Definition

private 
    variable
        ℓ ℓ' : Level

infixr 50 _:,_
infixr 49 _+~_
data Vec (A : Set ℓ) : ℕ → Set ℓ where 
    ⟨⟩ : Vec A 0
    _:,_ : {n : ℕ} → A → Vec A n → Vec A (ℕ.succ n)

length : {A : Set ℓ} {n : ℕ} → Vec A n → ℕ
length {n = n} _ = n

_+~_ : {A : Set ℓ} {m n : ℕ} → Vec A m → Vec A n → Vec A (m + n) 
_+~_ {n = n} ⟨⟩ ys rewrite +.comm 0 n = ys
_+~_ {m = ℕ.succ m} {n = n} (x :, xs) ys 
    rewrite +.assoc m 1 n ➤ (λ u → m + u) ◈ +.comm 1 n ➤` +.assoc m n 1 
    = x :, (xs +~ ys)

head : {A : Set ℓ} {n : ℕ} → Vec A (ℕ.succ n) → A
head (x :, xs) = x