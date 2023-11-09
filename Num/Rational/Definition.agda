module Num.Rational.Definition where
open import Control.Function.Util hiding (id)
open import Logic.Quantifier public
open import Logic.Connective public
open import Relation.Equality as ≡ using (_≡_; _≡⟨_⟩_; _≡⟨'_⟩_; _≡⟨⟩_; _∎; _◈_; _≡➤_; _≡➤`_)
open import Relation.Equivalance as ≃ hiding (trans; symm; refl)
open import Num.Natural.Definition as ℕ: using (ℕ; succ)
open import Num.Integer.Definition as ℤ: hiding (_≅_; _≇_; abs; module ≅)
open import Num.Integer.Algebra as ℤ 
open import Logic.Absurdum

infix 65 _÷_asℚ_
infix 40 _≅_

data ℚ : Set where
    _÷_asℚ_ : (x y : ℤ) → (¬ y ℤ:.≅ 0z) → ℚ

0q : ℚ
0q = 0z ÷ (1 − 0) asℚ λ()

1q : ℚ
1q = (1 − 0) ÷ (1 − 0) asℚ λ()

abs : ℚ → ℚ
abs x@(p@(p1 − p2) ÷ q@(q1 − q2) asℚ q≠0) with ℤ:.trichotomy p | ℤ:.trichotomy q 
... | rgt p≅0 | _ = x
... | lft _ | rgt q≅0 = ecq $ q≠0 q≅0
... | lft (rgt (p-1 :, p-)) | lft (rgt (q-1 :, q-)) = (p2 − p1) ÷ (q2 − q1) asℚ q≠0 ∘ ≡.symm
... | lft (rgt (p-1 :, p-)) | lft (lft (q-1 :, q+)) = (p2 − p1) ÷ q asℚ q≠0
... | lft (lft (p-1 :, p+)) | lft (rgt (q-1 :, q-)) = p ÷ (q2 − q1) asℚ q≠0 ∘ ≡.symm
... | lft (lft (p-1 :, p+)) | lft (lft (q-1 :, q+)) = p ÷ q asℚ q≠0

_≅_ : ℚ → ℚ → Set
p ÷ q asℚ q≠0 ≅ r ÷ s asℚ s≠0 = p * s ℤ:.≅ r * q

_≇_ : ℚ → ℚ → Set
x ≇ y = ¬ x ≅ y

module ≅ where
    refl : {x : ℚ} → x ≅ x
    refl {p ÷ q asℚ q≠0} = ≃.refl

    symm : {x y : ℚ} → x ≅ y → y ≅ x
    symm {p ÷ q asℚ q≠0} {r ÷ s asℚ s≠0} x≅y = ≃.symm x≅y 

    trans : {x y z : ℚ} → x ≅ y → y ≅ z → x ≅ z
    trans {p ÷ q asℚ q≠0} {r ÷ s asℚ s≠0} {u ÷ v asℚ v≠0} x≅y y≅z with ℤ:.decidable-0 r 
    ... | lft r≅0 = 
            p * v 
        ≃⟨ ℤ.*.cong p≅0 ≃.refl ⟩
            0z * v
        ≃⟨ ℤ.*.zeroL v ⟩
            0z
        ≃⟨ ≃.symm $ ℤ.*.zeroL q ⟩
            0z * q
        ≃⟨ ℤ.*.cong (≃.symm u≅0) ≃.refl ⟩
            u * q
        □
        where
            p≅0 = ℤ.*.no-0divisor p s (
                    p * s
                ≃⟨ x≅y ⟩
                    r * q
                ≃⟨ ℤ.*.cong r≅0 ≃.refl ⟩
                    0z * q
                ≃⟨ ℤ.*.zeroL q ⟩
                    0z
                □) s≠0
            u≅0 = ℤ.*.no-0divisor u s (
                    u * s
                ≃⟨ ≃.symm $ y≅z ⟩
                    r * v
                ≃⟨ ℤ.*.cong r≅0 ≃.refl ⟩
                    0z * v
                ≃⟨ ℤ.*.zeroL v ⟩
                    0z
                □) s≠0
    ... | rgt r≠0 = ℤ.*.canc (p * v) (u * q) (s * r) (λ s*r≅0 → s≠0 $ ℤ.*.no-0divisor s r s*r≅0 r≠0) $
            p * v * (s * r) 
        ≃⟨ ℤ.*.assoc p v (s * r) ⟩
            p * (v * (s * r))
        ≃⟨ ℤ.*.cong ≃.refl (ℤ.*.comm v (s * r)) ⟩
            p * (s * r * v)
        ≃⟨ ℤ.*.cong ≃.refl (ℤ.*.assoc s r v) ⟩
            p * (s * (r * v))
        ≃⟨ ≃.symm $ ℤ.*.assoc p s (r * v) ⟩
            p * s * (r * v)
        ≃⟨ ℤ.*.cong x≅y y≅z ⟩
            r * q * (u * s)
        ≃⟨ ℤ.*.assoc r q (u * s) ⟩
            r * (q * (u * s))
        ≃⟨ ℤ.*.comm r (q * (u * s)) ⟩
            q * (u * s) * r
        ≃⟨ ℤ.*.cong (≃.symm $ ℤ.*.assoc q u s) ≃.refl ⟩
            q * u * s * r
        ≃⟨ ℤ.*.assoc (q * u) s r ⟩
            q * u * (s * r)
        ≃⟨ ℤ.*.cong (ℤ.*.comm q u) ≃.refl ⟩
            u * q * (s * r)
        □

    instance
        ≅-Trans : Trans _≅_
        Trans.trans ≅-Trans {p ÷ q asℚ q≠0} {r ÷ s asℚ s≠0} {u ÷ v asℚ v≠0} x≅y y≅z 
            = trans {p ÷ q asℚ q≠0} {r ÷ s asℚ s≠0} {u ÷ v asℚ v≠0} x≅y y≅z
            
        ≅-Symm : Symm _≅_
        Symm.symm ≅-Symm {p ÷ q asℚ q≠0} {r ÷ s asℚ s≠0} x≅y = symm {p ÷ q asℚ q≠0} {r ÷ s asℚ s≠0} x≅y

        ≅-Refl : Refl _≅_
        Refl.refl ≅-Refl {p ÷ q asℚ q≠0} = refl {p ÷ q asℚ q≠0} 

        ≅-Eqv : Eqv _≅_
        ≅-Eqv = record
            {   -Trans = ≅-Trans
            ;   -Symm = ≅-Symm
            ;   -Refl = ≅-Refl
            }

        ℚ-EqvSet : EqvSet ℚ
        EqvSet._≃_ ℚ-EqvSet = _≅_