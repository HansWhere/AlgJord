module Algebra.Permutation where
open import Agda.Primitive using (Level)
open import Control.List.Vector.Definition
open import Control.List.Definition
open import Num.Natural.Definition as ℕ using (ℕ; succ; zero)
open import Control.Finite.Definition
open import Relation.Equality as ≡ using (_≡_; _≡⟨_⟩_; _≡⟨'_⟩_; _≡⟨⟩_; _∎; _◈_)

private 
    variable
        ℓ : Level

-- switch* : {n : ℕ} → Fin n → {A : Set ℓ} → Vec A n → Vec A n
-- switch* ⒩ ⟨⟩ = ⟨⟩
-- switch* ⒩ (x :, ⟨⟩) = x :, ⟨⟩
-- switch* ⑴ (x₁ :, x₂ :, xs) = x₂ :, x₁ :, xs
-- switch* (nxt ⒩) (x₁ :, x₂ :, xs) = x₁ :, switch* ⒩ (x₂ :, xs)

-- swap* : {n : ℕ} → Fin n → Fin n → {A : Set ℓ} → Vec A n → Vec A n
-- swap* {n = zero} _ _ _ = ⟨⟩
-- swap* ⑴ ⑴ xs = xs
-- swap* ⑴ ⑵ xs = switch* ⑴ xs
-- swap* ⑵ ⑴ xs = switch* ⑴ xs
-- swap* {n = succ (succ n)} (fst {succ (succ n)}) (nxt (nxt ⒩)) xs = 
--     switch* (nxt ⒩) (swap* ⑴ (nxt ⒩) (switch* (nxt ⒩) xs))
-- swap* (nxt (nxt ⒨)) ⑴ xs = switch* (nxt ⒨) (swap* (nxt ⒨) ⑴ (switch* (nxt ⒨) xs))
-- swap* (nxt ⒨) (nxt ⒩) ⟨⟩ = ⟨⟩
-- swap* (nxt ⒨) ⒩ (x :, xs) = x :, (swap* ⒨ ⒩ xs)

switch : {n : ℕ} → Fin n → {A : Set ℓ} → List A → List A
switch ⒩ [] = []
switch ⒩ (x :: []) = x :: []
switch ⑴ (x₁ :: x₂ :: xs) = x₂ :: x₁ :: xs
switch (nxt ⒩) (x₁ :: x₂ :: xs) = x₁ :: switch ⒩ (x₂ :: xs)

swap : {n : ℕ} → Fin n → Fin n → {A : Set ℓ} → List A → List A
swap ⑴ ⑴ xs = xs
swap {n = succ n} (nxt ⒨) (nxt ⒩) xs = switch ⒨ (switch ⒩ (swap {n = n} ⒨ ⒩ (switch ⒩ (switch ⒨ xs)))) 
swap {n = n} ⑴ ⑵ xs = switch {n = n} ⑴ xs
swap {n = n} ⑵ ⑴ xs = switch {n = n} ⑴ xs
swap ⑴ (nxt (nxt ⒩)) xs = switch (nxt ⒩) (swap ⑴ (nxt ⒩) (switch (nxt ⒩) xs)) 
swap (nxt (nxt ⒨)) ⑴ xs = switch (nxt ⒨) (swap (nxt ⒨) ⑴ (switch (nxt ⒨) xs))

cycle : {n : ℕ} → List (Fin n) → {A : Set ℓ} → List A → List A
cycle [] xs = xs
cycle (⒩ :: []) xs = xs
cycle (⒨ :: ⒩ :: ⒩s) xs = cycle (⒩ :: ⒩s) (swap ⒨ ⒩ xs)

perm : {n : ℕ} → List (List (Fin n)) → {A : Set ℓ} → List A → List A
perm [] xs = xs
perm (c :: cs) xs = perm cs (cycle c xs)

