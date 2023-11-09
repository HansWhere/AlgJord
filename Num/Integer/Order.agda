module Num.Integer.Order where
open import Control.Function.Util hiding (id)
open import Relation.Equality as ≡ using (_≡_; _≡⟨_⟩_; _≡⟨'_⟩_; _≡⟨⟩_; _∎; _◈_)
open import Num.Natural.Definition
open import Num.Natural.Algebra as ℕ renaming (_+_ to _⊹_)
open import Relation.Order as ≤ using (Trans; _➤_; Refl; Antisymm; Total; PreOrd; PartialOrd; TotalOrd; _≤⟨_⟩_; _≤⟨⟩_; _□)
open import Num.Natural.Order as ℕ≤ using () renaming (_≤_ to _-≤_)
open import Num.Integer.Definition as ℤ renaming (_−_ to _−_)
open import Logic.Connective using (_∧_; _,_; _∨_; lft; rgt)

infix 40 _≤_
_≤_ : ℤ → ℤ → Set
(a − b) ≤ (c − d) = a ⊹ d -≤ c ⊹ b

_<_ : ℤ → ℤ → Set
x < y = x ≤ y ∧ x ℤ.≇ y

refl : {x : ℤ} → x ≤ x
refl {a − b} = ℕ≤.refl

antisymm : {x y : ℤ} → x ≤ y → y ≤ x → x ≅ y
antisymm {a − b} {c − d} x≤y y≤x rewrite ℕ≤.antisymm x≤y y≤x = ℕ.+.comm c b

trans : {x y z : ℤ} → x ≤ y → y ≤ z → x ≤ z
trans {a − b} {c − d} {e − f} x≤y y≤z = ℕ≤.+.monotone' {a ⊹ f} {e ⊹ b} {c ⊹ d} {c ⊹ d} (ℕ≤.≡⇨≤ ≡.refl) $
        a ⊹ f ⊹ (c ⊹ d)
    ≤⟨ ℕ≤.≡⇨≤ eq1 ⟩
        a ⊹ d ⊹ (c ⊹ f)
    ≤⟨ ℕ≤.+.monotone x≤y y≤z ⟩
        c ⊹ b ⊹ (e ⊹ d)
    ≤⟨ ℕ≤.≡⇨≤ eq2 ⟩
        e ⊹ b ⊹ (c ⊹ d)
    □
    where
        ineq1 = ℕ≤.+.monotone x≤y y≤z
        eq1 =   a ⊹ f ⊹ (c ⊹ d)
            ≡⟨ ℕ.+.assoc a f (c ⊹ d) ⟩
                a ⊹ (f ⊹ (c ⊹ d))
            ≡⟨ (λ u → a ⊹ u) ◈ ℕ.+.comm f (c ⊹ d) ⟩
                a ⊹ (c ⊹ d ⊹ f)
            ≡⟨ (λ u → a ⊹ (u ⊹ f)) ◈ ℕ.+.comm c d ⟩
                a ⊹ (d ⊹ c ⊹ f)
            ≡⟨ (λ u → a ⊹ u) ◈ ℕ.+.assoc d c f ⟩
                a ⊹ (d ⊹ (c ⊹ f))
            ≡⟨' ℕ.+.assoc a d (c ⊹ f) ⟩
                a ⊹ d ⊹ (c ⊹ f)
            ∎
        eq2 =   c ⊹ b ⊹ (e ⊹ d)
            ≡⟨' ℕ.+.assoc (c ⊹ b) e d ⟩
                c ⊹ b ⊹ e ⊹ d
            ≡⟨ (λ u → u ⊹ d) ◈ ℕ.+.assoc c b e ⟩
                c ⊹ (b ⊹ e) ⊹ d
            ≡⟨ (λ u → u ⊹ d) ◈ ℕ.+.comm c (b ⊹ e) ⟩
                b ⊹ e ⊹ c ⊹ d
            ≡⟨ (λ u → u ⊹ c ⊹ d) ◈ ℕ.+.comm b e ⟩
                e ⊹ b ⊹ c ⊹ d
            ≡⟨ ℕ.+.assoc (e ⊹ b) c d ⟩
                e ⊹ b ⊹ (c ⊹ d)
            ∎

0≤abs : (x : ℤ) → ℤ.0z ≤ ℤ.abs x
0≤abs x@(x1 − x2) with ℤ.trichotomy x 
... | rgt x≅0 rewrite ℕ.+.comm 0 x2 = ℕ≤.≡⇨≤ $ ≡.symm x≅0
... | lft (rgt (n :, 0<x)) rewrite ≡.symm 0<x | ℕ.+.comm x1 (succ n) = ℕ≤.+.monotone ℕ≤.zero (ℕ≤.refl)
... | lft (lft (n :, x<0)) rewrite x<0 | ℕ.+.comm x2 (succ n) = ℕ≤.+.monotone ℕ≤.zero (ℕ≤.refl)

-- total : (x y : ℕ) → x ≤ y ∨ y ≤ x 
-- total (ℕ.succ x) (ℕ.succ y) with total x y 
-- ...    |   lft x≤y = lft (succ x≤y)
-- ...    |   rgt y≤x = rgt (succ y≤x)
-- total ℕ.zero y = lft zero
-- total (ℕ.succ x) ℕ.zero = rgt zero 
