module Num.Integer.PositiveAndNegsuc.Algebra where
open import Relation.Equality as ≡ using (_≡_; _≡⟨_⟩_; _≡⟨'_⟩_; _≡⟨_⟩'_; _≡⟨'_⟩'_; _≡⟨⟩_; _∎; _◈_)
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

    -- assoc : (x y z : ℤ) → x + y + z ≡ x + (y + z)
    -- assoc (pos x) (pos y) (pos z) = pos ◈ ℕ.+.assoc x y z
    -- assoc (nsc x) (nsc y) (nsc z) = nsc ◈ ℕ.+.assoc x y z 
    -- Not Done
        
    