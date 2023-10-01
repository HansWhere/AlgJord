module Num.Integer.Order where
open import Relation.Equality as ≡ using (_≡_; _≡⟨_⟩_; _≡⟨'_⟩_; _≡⟨⟩_; _∎; _◈_)
open import Num.Natural.Algebra as ℕ
open ℕ.+ using () renaming (_+_ to _⊹_)
open import Num.Natural.Order as ℕ≤ using () renaming (_≤_ to _-≤_)
open import Num.Integer.Definition as ℤ using (ℤ; _≅_) renaming (_−_ to _-−_)
open import Logic.Connective using (_∧_; _⹁_; _∨_; lft; rgt)

infix 40 _≤_
_≤_ : ℤ → ℤ → Set
(a -− b) ≤ (c -− d) = a ⊹ d -≤ c ⊹ b

refl : {x : ℤ} → x ≤ x
refl {a -− b} = ℕ≤.refl

-- inv-succ≤ : {x y : ℤ} → ℕ.succ x ≤ ℕ.succ y → x ≤ y
-- inv-succ≤ (succ x≤y) = x≤y

-- inv-zero≤ : {x : ℕ} → x ≤ ℕ.zero → x ≡ ℕ.zero 
-- inv-zero≤ zero = ≡.refl

antisymm : {x y : ℤ} → x ≤ y → y ≤ x → x ≅ y
antisymm {a -− b} {c -− d} x≤y y≤x rewrite ℕ≤.antisymm x≤y y≤x = ℕ.+.comm c b

trans : {x y z : ℤ} → x ≤ y → y ≤ z → x ≤ z
trans {a -− b} {c -− d} {e -− f} x≤y y≤z = {!   !} --ℕ≤.+.monotone x≤y y≤z

-- total : (x y : ℕ) → x ≤ y ∨ y ≤ x 
-- total (ℕ.succ x) (ℕ.succ y) with total x y 
-- ...    |   lft x≤y = lft (succ x≤y)
-- ...    |   rgt y≤x = rgt (succ y≤x)
-- total ℕ.zero y = lft zero
-- total (ℕ.succ x) ℕ.zero = rgt zero 
