module Num.Integer.PositiveAndNegsuc.Algebra where
open import Relation.Equality as ≡ using (_≡_; _≡⟨_⟩_; _≡⟨'_⟩_; _≡⟨⟩_; _∎; _◈_)
open import Num.Integer.PositiveAndNegsuc.Definition as ℤ using (ℤ; pos; nsc; ℕ; zero; succ)
import Num.Natural.Algebra as ℕ

module + where
    infixl 60 _+_
    _+_ : ℤ → ℤ → ℤ
    pos x + pos y = pos (x ℕ.+.+ y)
    nsc x + nsc y = nsc (x ℕ.+.+ y)
    pos x + nsc y = x ℤ.− succ y 
    nsc x + pos y = y ℤ.− succ x 

    comm : (x y : ℤ) → x + y ≡ y + x 
    comm (pos x) (pos y) = pos ◈ ℕ.+.comm x y
    comm (nsc x) (nsc y) = nsc ◈ ℕ.+.comm x y 
    comm (pos x) (nsc y) = ≡.refl
    comm (nsc x) (pos y) = ≡.refl

    left-iden : (x : ℤ) → pos zero + x ≡ x
    left-iden (pos x) = pos zero + pos x 
        ≡⟨⟩ pos (zero ℕ.+.+ x)
        ≡⟨ pos ◈ ℕ.+.left-iden x ⟩ pos x ∎  
    left-iden (nsc x) = ≡.refl

    right-iden : (x : ℤ) → x + pos zero ≡ x
    right-iden (pos x) = ≡.refl
    right-iden (nsc x) = ≡.refl

    assoc : (x y z : ℤ) → x + y + z ≡ x + (y + z)
    assoc (pos x) (pos y) (pos z) = pos ◈ ℕ.+.assoc x y z

    assoc (pos zero) (pos zero) (nsc z) = ≡.refl
    assoc (pos (succ x)) (pos zero) (nsc z) = ≡.refl
    assoc (pos zero) (pos (succ y)) (nsc z) = 
            pos zero + pos (succ y) + nsc z
        ≡⟨ (λ w → w + nsc z) ◈ left-iden (pos (succ y)) ⟩
            pos (succ y) + pos zero + nsc z
        ≡⟨⟩
            pos (succ y) + nsc z
        ≡⟨' left-iden (pos (succ y) + nsc z) ⟩
            pos zero + (pos (succ y) + nsc z)
        ∎ 
    assoc (pos (succ x)) (pos (succ y)) (nsc zero) = ≡.refl
    assoc (pos (succ x)) (pos (succ y)) (nsc (succ z)) = assoc (pos (succ x)) (pos y) (nsc z)

    assoc (pos zero) (nsc y) (pos z) = 
            pos zero + nsc y + pos z
        ≡⟨ (λ w → w + pos z) ◈ left-iden (nsc y) ⟩
            (nsc y + pos z)
        ≡⟨' left-iden (nsc y + pos z) ⟩
            pos zero + (nsc y + pos z)
        ∎
    assoc (pos (succ x)) (nsc zero) (pos z) = _
        --     pos (succ x) + nsc zero + pos z
        -- ≡⟨⟩
        --     succ x ℤ.− succ zero + pos z
        -- ≡⟨⟩
        --     x + pos z






    assoc (nsc x) (pos y) (pos z) = _
    assoc (pos x) (nsc y) (nsc z) = _
    assoc (nsc x) (pos y) (nsc z) = _
    assoc (nsc x) (nsc y) (pos z) = _
    assoc (nsc x) (nsc y) (nsc z) = nsc ◈ ℕ.+.assoc x y z 
    
    -- Not Done
        
    