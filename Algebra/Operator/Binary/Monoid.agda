module Algebra.Operator.Binary.Monoid where
open import Agda.Primitive using (Level)
open import Algebra.Operator.Binary.Property using (foldl; foldli; Assoc; assoc; Comm; comm; Iden; ε; idenl; idenr) public
open import Control.List.Definition
open import Relation.Equality as ≡ using (_≡_; _≡⟨_⟩_; _≡⟨'_⟩_; _≡⟨⟩_; _∎; _◈_; _➤_)
open import Num.Natural.Definition as ℕ using (ℕ; succ; zero)
open import Control.Finite.Definition
open import Algebra.Permutation

private 
    variable
        ℓ : Level

record Monoid {A : Set ℓ} (_*_ : A → A → A): Set ℓ where 
    field 
        overlap ⦃ -Iden ⦄ : Iden _*_
        overlap ⦃ -Assoc ⦄ : Assoc _*_
open Monoid ⦃...⦄ public

private
    comm-switch : {A : Set ℓ} (_*_ : A → A → A) ⦃ _ : Assoc _*_ ⦄ ⦃ _ : Comm _*_ ⦄ 
        {n : ℕ} (⒩ : Fin n) (i : A) (xs : List A) 
        → foldl _*_ i xs ≡ foldl _*_ i (switch ⒩ xs)
    comm-switch _*_ ⒩ i [] = ≡.refl
    comm-switch _*_ ⒩ i (x :: []) = ≡.refl
    comm-switch _*_ ⑴ i (x₁ :: x₂ :: xs) = 
            foldl _*_ ((i * x₁) * x₂) xs 
        ≡⟨ (λ u → foldl _*_ u xs) ◈ assoc i x₁ x₂ ⟩
            foldl _*_ (i * (x₁ * x₂)) xs
        ≡⟨ (λ u → foldl _*_ (i * u) xs) ◈ comm x₁ x₂ ⟩
            foldl _*_ (i * (x₂ * x₁)) xs
        ≡⟨' (λ u → foldl _*_ u xs) ◈ assoc i x₂ x₁ ⟩
            foldl _*_ ((i * x₂) * x₁) xs
        ∎
    comm-switch _*_ (nxt ⒩) i (x₁ :: x₂ :: xs) = 
            foldl _*_ ((i * x₁) * x₂) xs
        ≡⟨⟩
            foldl _*_ (i * x₁) (x₂ :: xs)
        ≡⟨ comm-switch _*_ ⒩ (i * x₁) (x₂ :: xs) ⟩
            foldl _*_ (i * x₁) (switch ⒩ (x₂ :: xs)) 
        ∎
    
    comm-swap : {A : Set ℓ} (_*_ : A → A → A) ⦃ _ : Assoc _*_ ⦄ ⦃ _ : Comm _*_ ⦄ 
        {n : ℕ} (⒨ : Fin n) (⒩ : Fin n) (i : A) (xs : List A) 
        → foldl _*_ i xs ≡ foldl _*_ i (swap ⒨ ⒩ xs)
    comm-swap _*_ ⑴ ⑴ i xs = ≡.refl 
    comm-swap _*_ {n = succ n} (nxt ⒨) (nxt ⒩) i xs = 
            foldl _*_ i xs 
        ≡⟨ comm-switch _*_ ⒨ i xs ⟩
            foldl _*_ i (switch ⒨ xs)
        ≡⟨ comm-switch _*_ ⒩ i (switch ⒨ xs) ⟩
            foldl _*_ i (switch ⒩ (switch ⒨ xs))
        ≡⟨ comm-swap _*_ ⒨ ⒩ i (switch ⒩ (switch ⒨ xs)) ⟩
            foldl _*_ i (swap ⒨ ⒩ (switch ⒩ (switch ⒨ xs)))
        ≡⟨ comm-switch _*_ ⒩ i (swap ⒨ ⒩ (switch ⒩ (switch ⒨ xs))) ⟩
            foldl _*_ i (switch ⒩ (swap ⒨ ⒩ (switch ⒩ (switch ⒨ xs))))
        ≡⟨ comm-switch _*_ ⒨ i (switch ⒩ (swap ⒨ ⒩ (switch ⒩ (switch ⒨ xs)))) ⟩
            foldl _*_ i (switch ⒨ (switch ⒩ (swap ⒨ ⒩ (switch ⒩ (switch ⒨ xs)))))
        ∎ 
    comm-swap _*_ {n = n} ⑴ ⑵ i xs = comm-switch _*_ ⑴ i xs
    comm-swap _*_ {n = n} ⑵ ⑴ i xs = comm-switch _*_ ⑴ i xs
    comm-swap _*_ {n = succ (succ n)} ⑴ (nxt (nxt ⒩)) i xs = 
            foldl _*_ i xs 
        ≡⟨ comm-switch _*_ (nxt ⒩) i xs ⟩
            foldl _*_ i (switch (nxt ⒩) xs)
        ≡⟨ comm-swap _*_ {n = succ n} ⑴ (nxt ⒩) i (switch (nxt ⒩) xs) ⟩
            foldl _*_ i (swap ⑴ (nxt ⒩) (switch (nxt ⒩) xs))
        ≡⟨ comm-switch _*_ (nxt ⒩) i (swap ⑴ (nxt ⒩) (switch (nxt ⒩) xs)) ⟩
            foldl _*_ i (switch (nxt ⒩) (swap ⑴ (nxt ⒩) (switch (nxt ⒩) xs)))
        ∎
    comm-swap _*_ {n = succ (succ n)} (nxt (nxt ⒨)) ⑴ i xs = 
            foldl _*_ i xs 
        ≡⟨ comm-switch _*_ (nxt ⒨) i xs ⟩
            foldl _*_ i (switch (nxt ⒨) xs)
        ≡⟨ comm-swap _*_ {n = succ n} (nxt ⒨) ⑴ i (switch (nxt ⒨) xs) ⟩
            foldl _*_ i (swap (nxt ⒨) ⑴ (switch (nxt ⒨) xs))
        ≡⟨ comm-switch _*_ (nxt ⒨) i (swap (nxt ⒨) ⑴ (switch (nxt ⒨) xs)) ⟩
            foldl _*_ i (switch (nxt ⒨) (swap (nxt ⒨) ⑴ (switch (nxt ⒨) xs)))
        ∎

    comm-cycle : {A : Set ℓ} (_*_ : A → A → A) ⦃ _ : Assoc _*_ ⦄ ⦃ _ : Comm _*_ ⦄ 
        {n : ℕ} (⒩s : List (Fin n)) (i : A) (xs : List A) 
        → foldl _*_ i xs ≡ foldl _*_ i (cycle ⒩s xs)
    comm-cycle _*_ [] i xs = ≡.refl
    comm-cycle _*_ (⒩ :: []) i xs = ≡.refl
    comm-cycle _*_ {n = n} (⒨ :: ⒩ :: ⒩s) i xs = 
            foldl _*_ i xs
        ≡⟨ comm-swap _*_ ⒨ ⒩ i xs ⟩
            foldl _*_ i (swap ⒨ ⒩ xs)
        ≡⟨ comm-cycle _*_ {n = n} (⒩ :: ⒩s) i (swap ⒨ ⒩ xs) ⟩
            foldl _*_ i (cycle (⒩ :: ⒩s) (swap ⒨ ⒩ xs))
        ∎

comm∀ : {A : Set ℓ} (_*_ : A → A → A) ⦃ _ : Assoc _*_ ⦄ ⦃ _ : Comm _*_ ⦄ {n : ℕ} (pm : List (List (Fin n))) (i : A) (xs : List A) 
    → foldl _*_ i xs ≡ foldl _*_ i (perm pm xs)
comm∀ _*_ [] i xs = ≡.refl
comm∀ _*_ (c :: cs) i xs = 
        foldl _*_ i xs
    ≡⟨ comm-cycle _*_ c i xs ⟩
        foldl _*_ i (cycle c xs)
    ≡⟨ comm∀ _*_ cs i (cycle c xs) ⟩
        foldl _*_ i (perm cs (cycle c xs))
    ∎