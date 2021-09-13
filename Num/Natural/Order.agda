module Num.Natural.Order where
open import Relation.Equality as ≡ using (_≡_; _≡⟨_⟩_; _≡⟨'_⟩_; _≡⟨⟩_; _∎; _◈_)
open import Num.Natural.Definition as ℕ using (ℕ)
open import Logic.Connective using (_∧_; _,_; _∨_; lft; rgt)

infix 40 _≤_
data _≤_ : ℕ → ℕ → Set where
    zero : {x : ℕ} → ℕ.zero ≤ x 
    succ : {x y : ℕ} → x ≤ y → ℕ.succ x ≤ ℕ.succ y

refl : {x : ℕ} → x ≤ x
refl {ℕ.zero} = zero
refl {ℕ.succ x} = succ refl

inv-succ≤ : {x y : ℕ} → ℕ.succ x ≤ ℕ.succ y → x ≤ y
inv-succ≤ (succ x≤y) = x≤y

inv-zero≤ : {x : ℕ} → x ≤ ℕ.zero → x ≡ ℕ.zero 
inv-zero≤ zero = ≡.refl

antisymm : {x y : ℕ} → x ≤ y → y ≤ x → x ≡ y
antisymm zero zero = ≡.refl
antisymm (succ x≤y) (succ y≤z) = ℕ.succ ◈ antisymm x≤y y≤z

trans : {x y z : ℕ} → x ≤ y → y ≤ z → x ≤ z
trans zero _ = zero
trans (succ x≤y) (succ y≤z) = succ (trans x≤y y≤z) 

total : (x y : ℕ) → x ≤ y ∨ y ≤ x 
total x ℕ.zero = rgt zero 
total ℕ.zero y = lft zero
total (ℕ.succ x) (ℕ.succ y) with total x y 
...    |   lft x≤y = lft (succ x≤y)
...    |   rgt y≤x = rgt (succ y≤x)