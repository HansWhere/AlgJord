module Algebra.Operator.Binary.Property where
open import Agda.Primitive using (Level)
open import Relation.Equality as ≡ using (_≡_; _≡⟨_⟩_; _≡⟨'_⟩_; _≡⟨⟩_; _∎; _◈_)
open import Relation.Equivalance as ≃ using (Eqv; _≃⟨⟩_; _≃⟨'_⟩_; _≃⟨_⟩_; _□; _➤_)
open import Logic.Connective using (_∧_; _,_)
open import Algebra.Operator.Binary.Free public
open import Control.List.Definition
open import Algebra.Permutation
-- open import Num.Natural.Definition as ℕ using (ℕ; succ; zero)

private 
    variable
        ℓ : Level

foldl : {A : Set ℓ} (_*_ : A → A → A) → A → List A → A
foldl _*_ x₀ [] = x₀
foldl _*_ x₀ (x :: xs) = foldl _*_ (x₀ * x) xs 

foldr : {A : Set ℓ} (_*_ : A → A → A) → A → List A → A
foldr _*_ x₀ [] = x₀
foldr _*_ x₀ (x :: xs) = x₀ * foldl _*_ x xs 

record Assoc {A : Set ℓ} {_≃_ : A → A → Set ℓ} ⦃ _ : Eqv _≃_ ⦄ (_*_ : A → A → A) : Set ℓ where 
    field
        assoc : (x y z : A) → ((x * y) * z) ≃ (x * (y * z))
open Assoc ⦃...⦄ public

record Cong {A : Set ℓ} (_≃_ : A → A → Set ℓ) (_*_ : A → A → A) : Set ℓ where
    field 
        cong : {a b c d : A} → (a ≃ b) → (c ≃ d) → ((a * c) ≃ (b * d))
open Cong ⦃...⦄ public

{-# TERMINATING #-}
assoc∀l : {A : Set ℓ} {_≃_ : A → A → Set ℓ} ⦃ _ : Eqv _≃_ ⦄ (_*_ : A → A → A) ⦃ _ : Assoc _*_ ⦄ ⦃ _ : Cong _≃_ _*_ ⦄ (xs : Free A) 
    → (fold _*_ xs ≃ fold _*_ (assocl xs))
assoc∀l _*_ (pure x) = ≃.refl
assoc∀l _*_ (xs ◌ pure x) = cong (assoc∀l _*_ xs) ≃.refl
assoc∀l _*_ (xs ◌ (ys ◌ zs)) = ≃.symm (assoc (fold _*_ xs) (fold _*_ ys) (fold _*_ zs)) ➤ assoc∀l _*_ ((xs ◌ ys) ◌ zs)

record Comm {A : Set ℓ} {_≃_ : A → A → Set ℓ} ⦃ _ : Eqv _≃_ ⦄ (_*_ : A → A → A) : Set ℓ where 
    field
        comm : (x y : A) → (x * y) ≃ (y * x)
open Comm ⦃...⦄ public 

record Iden {A : Set ℓ} {_≃_ : A → A → Set ℓ} ⦃ _ : Eqv _≃_ ⦄ (_*_ : A → A → A) : Set ℓ where
    field 
        id : A
        idenL : (x : A) → (id * x) ≃ x
        idenR : (x : A) → (x * id) ≃ x
    iden : (x : A) → (id * x) ≃ x ∧ (x * id) ≃ x
    iden x = idenL x , idenR x
open Iden ⦃...⦄ public

foldli : {A : Set ℓ} (_*_ : A → A → A) ⦃ _ : Iden _*_ ⦄ → List A → A
foldli _*_ xs = foldl _*_ id xs 

foldri : {A : Set ℓ} (_*_ : A → A → A) ⦃ _ : Iden _*_ ⦄ → List A → A
foldri _*_ xs = foldr _*_ id xs 

record Distr {A : Set ℓ} {_≃_ : A → A → Set ℓ} ⦃ _ : Eqv _≃_ ⦄ (_+_ : A → A → A) (_*_ : A → A → A) : Set ℓ where 
    field
        distrL : (x y z : A) → (x * (y + z)) ≃ ((x * y) + (x * z))
        distrR : (x y z : A) → ((x + y) * z) ≃ ((x * z) + (y * z))
    distr : (x y z : A) → (x * (y + z)) ≃ ((x * y) + (x * z)) ∧ ((x + y) * z) ≃ ((x * z) + (y * z))
    distr x y z = distrL x y z , distrR x y z 
open Distr ⦃...⦄ public 
