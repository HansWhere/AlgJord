module Control.List.Vector.Util where
open import Control.List.Vector.Definition
open import Relation.Equality
open import Num.Natural.Definition using (ℕ)
open import Num.Natural.Algebra
open + using (_+_)
open import Agda.Primitive using (Level)


private 
    variable
        ℓ ℓ' : Level

infixr 49 _+~_

length : {A : Set ℓ} {n : ℕ} → Vec A n → ℕ
length {n = n} _ = n

_+~_ : {A : Set ℓ} {m n : ℕ} → Vec A m → Vec A n → Vec A (m + n) 
_+~_ {n = n} ⟨⟩ ys rewrite +.comm 0 n = ys
_+~_ {m = ℕ.succ m} {n = n} (x :, xs) ys 
    rewrite +.assoc m 1 n ➤ (λ u → m + u) ◈ +.comm 1 n ➤` +.assoc m n 1 
    = x :, (xs +~ ys)

head : {A : Set ℓ} {n : ℕ} → Vec A (ℕ.succ n) → A
head (x :, xs) = x