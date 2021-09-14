module Num.Integer.SubtractionClosure.Algebra where 
open import Num.Integer.SubtractionClosure.Definition as ℤ using (ℤ; _≃_) renaming (_−_ to _-−_)
import Num.Natural.Algebra as ℕ
open import Relation.Equality as ≡ using (_≡_; _≡⟨_⟩_; _≡⟨'_⟩_; _≡⟨⟩_; _∎; _◈_; _➤_)


module + where
    open ℕ.+ using () renaming (_+_ to _⊹_)
    infixl 60 _+_ 
    _+_ : ℤ → ℤ → ℤ
    (x₁ -− x₂) + (y₁ -− y₂) = (x₁ ⊹ y₁) -− (x₂ ⊹ y₂) 

    comm : (x y : ℤ) → x + y ≃ y + x 
    comm (x₁ -− x₂) (y₁ -− y₂) = ℕ.+.comm (x₁ ⊹ y₁) (y₂ ⊹ x₂) ➤ ≡.cong2 _⊹_ (ℕ.+.comm y₂ x₂) (ℕ.+.comm x₁ y₁)

    assoc : (x y z : ℤ) → x + y + z ≃ x + (y + z)
    assoc (x₁ -− x₂) (y₁ -− y₂) (z₁ -− z₂) = 
            (x₁ ⊹ y₁ ⊹ z₁) ⊹ (x₂ ⊹ (y₂ ⊹ z₂))
        ≡⟨ ℕ.+.comm (x₁ ⊹ y₁ ⊹ z₁) (x₂ ⊹ (y₂ ⊹ z₂)) ⟩ 
            (x₂ ⊹ (y₂ ⊹ z₂)) ⊹ (x₁ ⊹ y₁ ⊹ z₁)
        ≡⟨ ≡.cong2 _⊹_ (≡.symm (ℕ.+.assoc x₂ y₂ z₂)) (ℕ.+.assoc x₁ y₁ z₁) ⟩
            x₂ ⊹ y₂ ⊹ z₂ ⊹ (x₁ ⊹ (y₁ ⊹ z₁))
        ∎

    infixl 60 _−_
    _−_ : ℤ → ℤ → ℤ
    (x₁ -− x₂) − (y₁ -− y₂) = (x₁ ⊹ y₂) -− (y₁ ⊹ x₂)

    neg : ℤ → ℤ
    neg (x₁ -− x₂) = x₂ -− x₁

module * where
    open ℕ.* using () renaming (_*_ to _×_)
    open ℕ.+ using () renaming (_+_ to _⊹_)

    infixl 70 _*_ 
    _*_ : ℤ → ℤ → ℤ
    (x₁ -− x₂) * (y₁ -− y₂) = (x₁ × y₁ ⊹ x₂ × y₂) -− (x₁ × y₂ ⊹ x₂ × y₁)
    
    comm : (x y : ℤ) → x * y ≃ y * x 
    comm (x₁ -− x₂) (y₁ -− y₂) = 
            (x₁ × y₁ ⊹ x₂ × y₂) ⊹ (y₁ × x₂ ⊹ y₂ × x₁)
        ≡⟨ ℕ.+.comm (x₁ × y₁ ⊹ x₂ × y₂) (y₁ × x₂ ⊹ y₂ × x₁) ⟩
            (y₁ × x₂ ⊹ y₂ × x₁) ⊹ (x₁ × y₁ ⊹ x₂ × y₂)
        ≡⟨ (λ u → u ⊹ (x₁ × y₁ ⊹ x₂ × y₂)) ◈ (ℕ.+.comm (y₁ × x₂) (y₂ × x₁)) ⟩
            (y₂ × x₁ ⊹ y₁ × x₂) ⊹ (x₁ × y₁ ⊹ x₂ × y₂)
        ≡⟨ ≡.cong4 (λ a b c d → (a ⊹ b) ⊹ (c ⊹ d)) (ℕ.*.comm y₂ x₁) (ℕ.*.comm y₁ x₂) (ℕ.*.comm x₁ y₁) (ℕ.*.comm x₂ y₂) ⟩
            (x₁ × y₂ ⊹ x₂ × y₁) ⊹ (y₁ × x₁ ⊹ y₂ × x₂)
        ∎

    module to+ where
        open +
        ldistr : (x y z : ℤ) → x * (y + z) ≡ x * y + x * z 
        ldistr (x₁ -− x₂) (y₁ -− y₂) (z₁ -− z₂) = _
            


    -- assoc : (x y z : ℤ) → x * y * z ≃ x * (y * z)
    -- assoc (x₁ -− x₂) (y₁ -− y₂) (z₁ -− z₂) = _

    -- open import Num.Natural.Definition
    -- eg : {x₁ x₂ y₁ y₂ z₁ z₂ : ℕ} → 
    --     (x₁ × y₁ ⊹ x₂ × y₂) × z₁ ⊹ (x₁ × y₂ ⊹ x₂ × y₁) × z₂ ⊹
    --     (x₁ × (y₁ × z₂ ⊹ y₂ × z₁) ⊹ x₂ × (y₁ × z₁ ⊹ y₂ × z₂))
    --     ≡
    --     (x₁ × y₁ ⊹ x₂ × y₂) × z₂ ⊹ (x₁ × y₂ ⊹ x₂ × y₁) × z₁ ⊹
    --     (x₁ × (y₁ × z₁ ⊹ y₂ × z₂) ⊹ x₂ × (y₁ × z₂ ⊹ y₂ × z₁))