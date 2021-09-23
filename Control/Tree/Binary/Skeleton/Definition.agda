module Control.Tree.Binary.Skeleton.Definition where
open import Agda.Primitive using (Level)
open import Relation.Equality as ≡ 
open import Control.List.Definition
open import Num.Natural.Definition using (ℕ)
open import Num.Natural.Algebra as ℕ
open + using (_+_)

private 
    variable
        ℓ ℓ' : Level

infixl 66 _━_ _┳_ 
infixl 67 _┓
infixr 68 ┏_
data Skel : ℕ → Set where 
    ╻ : Skel 1
    _━_ : {m n : ℕ} → Skel m → Skel n → Skel (m + n)
︻ : Skel 2
︻ = ╻ ━ ╻
_┓ : {n : ℕ} → Skel n → Skel (ℕ.succ n)
xs ┓ = xs ━ ╻
┏_ : {n : ℕ} → Skel n → Skel (ℕ.succ n)
┏_ {n} xs rewrite +.comm n 1 = ╻ ━ xs
_┳_ : {m n : ℕ} → Skel m → Skel n → Skel (ℕ.succ (m + n))
_┳_ {m} {n} xs ys 
    rewrite +.assoc m n 1 ➤ (λ u → m + u) ◈ +.comm n 1 ➤` +.assoc m 1 n 
    = xs ━ ╻ ━ ys 

╻⋯┓ : (n : ℕ) → Skel (ℕ.succ n) 
╻⋯┓ 0 = ╻
╻⋯┓ (ℕ.succ n) = ╻⋯┓ n ┓

┏⋯╻ : (n : ℕ) → Skel (ℕ.succ n) 
┏⋯╻ 0 = ╻
┏⋯╻ (ℕ.succ n) = ┏ ┏⋯╻ n 

private 
    eg : Skel 7
    eg = ┏ ︻ ┓ ┳ ╻ ━ ╻