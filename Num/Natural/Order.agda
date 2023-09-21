module Num.Natural.Order where
open import Relation.Equality as ≡ using (_≡_; _≡⟨_⟩_; _≡⟨'_⟩_; _≡⟨⟩_; _∎; _◈_)
open import Relation.Order as ≤ using (Trans; _➤_; Refl; Antisymm; Total; PreOrd; PartialOrd; TotalOrd; _≤⟨_⟩_; _≤⟨⟩_; _□)
open import Num.Natural.Definition as ℕ using (ℕ)
open import Logic.Connective using (_∧_; _⹁_; _∨_; lft; rgt)

infix 40 _≤_
data _≤_ : ℕ → ℕ → Set where
    zero : {x : ℕ} → 0 ≤ x 
    succ : {x y : ℕ} → x ≤ y → ℕ.succ x ≤ ℕ.succ y

refl : {x : ℕ} → x ≤ x
refl {0} = zero
refl {ℕ.succ x} = succ refl

antisymm : {x y : ℕ} → x ≤ y → y ≤ x → x ≡ y
antisymm zero zero = ≡.refl
antisymm (succ x≤y) (succ y≤z) = ℕ.succ ◈ antisymm x≤y y≤z

trans : {x y z : ℕ} → x ≤ y → y ≤ z → x ≤ z
trans zero _ = zero
trans (succ x≤y) (succ y≤z) = succ (trans x≤y y≤z) 

total : (x y : ℕ) → x ≤ y ∨ y ≤ x 
total 0 y = lft zero
total (ℕ.succ x) 0 = rgt zero 
total (ℕ.succ x) (ℕ.succ y) with total x y 
...    |   lft x≤y = lft (succ x≤y)
...    |   rgt y≤x = rgt (succ y≤x)

instance
    ≤-Refl : Refl _≤_
    Refl.refl ≤-Refl = refl

    ≤-Antisymm : Antisymm _≤_
    Antisymm.antisymm ≤-Antisymm = antisymm

    ≤-Trans : Trans _≤_
    Trans.trans ≤-Trans = trans

    ≤-Total : Total _≤_
    Total.total ≤-Total = total

    ≤-PreOrd : PreOrd _≤_
    PreOrd.-Refl ≤-PreOrd = ≤-Refl

    ≤-PartialOrd : PartialOrd _≤_
    PartialOrd.-Antisymm ≤-PartialOrd = ≤-Antisymm

    ≤-TotalOrd : TotalOrd _≤_
    TotalOrd.-Total ≤-TotalOrd = ≤-Total

module + where
    open import Num.Natural.Algebra as ℕalg
    open +

    private
        inv-succ≤ : {x y : ℕ} → ℕ.succ x ≤ ℕ.succ y → x ≤ y
        inv-succ≤ (succ x≤y) = x≤y

        inv-zero≤ : {x : ℕ} → x ≤ 0 → x ≡ 0 
        inv-zero≤ zero = ≡.refl

        ≤succ : (x : ℕ) → x ≤ (ℕ.succ x)
        ≤succ 0 = zero
        ≤succ (ℕ.succ x) = succ (≤succ x)

        monotone0 : {a b : ℕ} → a ≤ b → (c : ℕ) → a ≤ b + c
        monotone0 a≤b 0 = a≤b
        monotone0 {a = 0} a≤b (ℕ.succ c) = zero
        monotone0 {a = ℕ.succ a} {b} a≤b (ℕ.succ c) = 
                ℕ.succ a
            ≤⟨ a≤b ⟩
                b
            ≤⟨ monotone0 refl c ⟩
                b + c
            ≤⟨ ≤succ (b + c) ⟩
                ℕ.succ (b + c)
            □

    monotone : {a b c d : ℕ} → a ≤ b → c ≤ d → a + c ≤ b + d
    monotone {d = d} a≤b zero = monotone0 a≤b d 
    monotone {c = ℕ.succ c} {d = ℕ.succ d} a≤b (succ c≤d) = succ (monotone a≤b c≤d) 

    monotone' : {a b c d : ℕ} → c ≤ d → a + d ≤ b + c → a ≤ b
    monotone' {a} {b} {0} {d} zero a+d≤b = 
            a
        ≤⟨ monotone refl zero ⟩
            a + d
        ≤⟨ a+d≤b ⟩
            b
        □
    monotone' {a} {b} {ℕ.succ c} {ℕ.succ d} (succ c≤d) (succ a+d≤b+c) = monotone' c≤d a+d≤b+c 

