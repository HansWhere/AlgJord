module Algebra.Operator.Binary.Free where
open import Agda.Primitive using (Level)
open import Control.List.Definition
open import Relation.Equality as ≡ using (_≡_; _≡⟨_⟩_; _≡⟨'_⟩_; _≡⟨⟩_; _∎; _◈_; _➤_)
open import Num.Natural.Definition as ℕ using (ℕ; succ; zero)

private 
    variable
        ℓ : Level

infixl 60 _◌_ _◐_ _◑_ _◍_

data Free (A : Set ℓ) : Set ℓ where
    pure : A → Free A
    _◌_ : Free A → Free A → Free A

_◐_ : {A : Set ℓ} → A → Free A → Free A
x ◐ fy = pure x ◌ fy
_◑_ : {A : Set ℓ} → Free A → A → Free A
fx ◑ y = fx ◌ pure y
_◍_ : {A : Set ℓ} → A → A → Free A
x ◍ y = pure x ◌ pure y

fold : {A : Set ℓ} → (_*_ : A → A → A) → Free A → A
fold _*_ (pure x) = x
fold _*_ (xs ◌ ys) = fold _*_ xs * fold _*_ ys

{-# TERMINATING #-}
assocl : {A : Set ℓ} → Free A → Free A
assocl (pure x) = pure x
assocl (xs ◌ pure y) = assocl xs ◌ pure y
assocl (xs ◌ (ys ◌ zs)) = assocl ((xs ◌ ys) ◌ zs)
-- Is there any way to tell Agda compiler I am terminating gently instead of forcing him to agree?

private 
    open import Num.Natural.Definition using (ℕ; succ; zero)
    eg1 : Free ℕ
    eg1 = 1 ◐ (2 ◍ 3) ◌ ((4 ◍ 5) ◑ 6)
    egg1 : Free ℕ
    egg1 = assocl eg1 

    eg2 : Free ℕ
    eg2 = 1 ◐ (2 ◐ (3 ◐ (4 ◐ (5 ◐ (6 ◐ (7 ◍ 8))))))
    egg2 : Free ℕ
    egg2 = assocl eg2 