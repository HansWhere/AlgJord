module Num.Integer.SubtractionClosure.Algebra where 
open import Num.Integer.SubtractionClosure.Definition as ℤ using (ℤ; _≅_) renaming (_−_ to _-−_)
import Num.Natural.Algebra as ℕ
open import Num.Natural.Definition using (zero)
open import Algebra.Operator.Binary.Property using (Free; assoc∀l; _◌_; _◍_; _◐_; _◑_)
open import Algebra.Operator.Binary.Monoid using (comm∀i)
open import Control.List.Definition
open import Control.Finite.Definition
open import Control.Function.Util using (_$_)
open import Relation.Equality as ≡ using (_≡_; _≡⟨_⟩_; _≡⟨'_⟩_; _≡⟨⟩_; _∎; _◈_; _≡➤_)
open import Relation.Equivalance
open import Algebra.Operator.Binary.Property using (Comm; Assoc; Distr; Iden; Cong)
open import Algebra.Operator.Binary.Monoid using (Monoid)


module + where
    open ℕ.+ using () renaming (_+_ to _⊹_)
    infixl 60 _+_ 
    _+_ : ℤ → ℤ → ℤ
    (x₁ -− x₂) + (y₁ -− y₂) = (x₁ ⊹ y₁) -− (x₂ ⊹ y₂) 

    comm : (x y : ℤ) → x + y ≅ y + x 
    comm (x₁ -− x₂) (y₁ -− y₂) = ℕ.+.comm (x₁ ⊹ y₁) (y₂ ⊹ x₂) ≡➤ ≡.cong2 _⊹_ (ℕ.+.comm y₂ x₂) (ℕ.+.comm x₁ y₁)

    assoc : (x y z : ℤ) → x + y + z ≅ x + (y + z)
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
    open ℕ.+ using (+-Monoid) renaming (_+_ to _⊹_)

    infixl 70 _*_ 
    _*_ : ℤ → ℤ → ℤ
    (x₁ -− x₂) * (y₁ -− y₂) = (x₁ × y₁ ⊹ x₂ × y₂) -− (x₁ × y₂ ⊹ x₂ × y₁)
    
    -- cong : {a b c d : A} → (a ≅ b) → (c ≅ d) → ((a * c) ≅ (b * d))
    -- cong {a₁ -− a₂} {b₁ -− b₂} {c₁ -− c₂} {d₁ -− d₂} a≅b c≅d

    comm : (x y : ℤ) → x * y ≅ y * x 
    comm (x₁ -− x₂) (y₁ -− y₂) = 
            (x₁ × y₁ ⊹ x₂ × y₂) ⊹ (y₁ × x₂ ⊹ y₂ × x₁)
        ≡⟨ ℕ.+.comm (x₁ × y₁ ⊹ x₂ × y₂) (y₁ × x₂ ⊹ y₂ × x₁) ⟩
            (y₁ × x₂ ⊹ y₂ × x₁) ⊹ (x₁ × y₁ ⊹ x₂ × y₂)
        ≡⟨ (λ u → u ⊹ (x₁ × y₁ ⊹ x₂ × y₂)) ◈ (ℕ.+.comm (y₁ × x₂) (y₂ × x₁)) ⟩
            (y₂ × x₁ ⊹ y₁ × x₂) ⊹ (x₁ × y₁ ⊹ x₂ × y₂)
        ≡⟨ ≡.cong4 (λ a b c d → (a ⊹ b) ⊹ (c ⊹ d)) (ℕ.*.comm y₂ x₁) (ℕ.*.comm y₁ x₂) (ℕ.*.comm x₁ y₁) (ℕ.*.comm x₂ y₂) ⟩
            (x₁ × y₂ ⊹ x₂ × y₁) ⊹ (y₁ × x₁ ⊹ y₂ × x₂)
        ∎

    module over+ where
        open +
        distrL : (x y z : ℤ) → x * (y + z) ≅ x * y + x * z 
        distrL (x₁ -− x₂) (y₁ -− y₂) (z₁ -− z₂) = 
                x₁ × (y₁ ⊹ z₁) ⊹ x₂ × (y₂ ⊹ z₂) ⊹ (x₁ × y₂ ⊹ x₂ × y₁ ⊹ (x₁ × z₂ ⊹ x₂ × z₁))
            ≡⟨ ≡.cong2 (λ a b → a ⊹ b ⊹ (x₁ × y₂ ⊹ x₂ × y₁ ⊹ (x₁ × z₂ ⊹ x₂ × z₁))) (ℕ.*.over+.distrL x₁ y₁ z₁) (ℕ.*.over+.distrL x₂ y₂ z₂)⟩
                x₁ × y₁ ⊹ x₁ × z₁ ⊹ (x₂ × y₂ ⊹ x₂ × z₂) ⊹ (x₁ × y₂ ⊹ x₂ × y₁ ⊹ (x₁ × z₂ ⊹ x₂ × z₁))
            ≡⟨ assoc∀l _⊹_ ((x₁ × y₁ ◍ x₁ × z₁) ◌ (x₂ × y₂ ◍ x₂ × z₂) ◌ ((x₁ × y₂ ◍ x₂ × y₁) ◌ (x₁ × z₂ ◍ x₂ × z₁)))⟩
                x₁ × y₁ ⊹ x₁ × z₁ ⊹ x₂ × y₂ ⊹ x₂ × z₂ ⊹ x₁ × y₂ ⊹ x₂ × y₁ ⊹ x₁ × z₂ ⊹ x₂ × z₁
            ≡⟨ (λ u → u ⊹ x₁ × z₁ ⊹ x₂ × y₂ ⊹ x₂ × z₂ ⊹ x₁ × y₂ ⊹ x₂ × y₁ ⊹ x₁ × z₂ ⊹ x₂ × z₁) ◈ ℕ.+.comm (x₁ × y₁) 0 ⟩
                0 ⊹ x₁ × y₁ ⊹ x₁ × z₁ ⊹ x₂ × y₂ ⊹ x₂ × z₂ ⊹ x₁ × y₂ ⊹ x₂ × y₁ ⊹ x₁ × z₂ ⊹ x₂ × z₁
            ≡⟨ comm∀i _⊹_ {8} [ [ ⑴ , ⑸ ] , [ ⑵ , ⑺ ] , [ ⑶ , ⑹ ] , [ ⑷ , ⑻ ] ] 
                    [ x₁ × y₁ , x₁ × z₁ , x₂ × y₂ , x₂ × z₂ , x₁ × y₂ , x₂ × y₁ , x₁ × z₂ , x₂ × z₁ ] ⟩
                0 ⊹ x₁ × y₂ ⊹ x₁ × z₂ ⊹ x₂ × y₁ ⊹ x₂ × z₁ ⊹ x₁ × y₁ ⊹ x₂ × y₂ ⊹ x₁ × z₁ ⊹ x₂ × z₂
            ≡⟨ (λ u → u ⊹ x₁ × z₂ ⊹ x₂ × y₁ ⊹ x₂ × z₁ ⊹ x₁ × y₁ ⊹ x₂ × y₂ ⊹ x₁ × z₁ ⊹ x₂ × z₂) ◈ ℕ.+.comm 0 (x₁ × y₂)⟩
                x₁ × y₂ ⊹ x₁ × z₂ ⊹ x₂ × y₁ ⊹ x₂ × z₁ ⊹ x₁ × y₁ ⊹ x₂ × y₂ ⊹ x₁ × z₁ ⊹ x₂ × z₂
            ≡⟨' assoc∀l _⊹_ ((x₁ × y₂ ◍ x₁ × z₂) ◌ (x₂ × y₁ ◍ x₂ × z₁) ◌ ((x₁ × y₁ ◍ x₂ × y₂) ◌ (x₁ × z₁ ◍ x₂ × z₂)))⟩
                (x₁ × y₂ ⊹ x₁ × z₂) ⊹ (x₂ × y₁ ⊹ x₂ × z₁) ⊹ (x₁ × y₁ ⊹ x₂ × y₂ ⊹ (x₁ × z₁ ⊹ x₂ × z₂))
            ≡⟨ ≡.cong2 (λ a b → a ⊹ b ⊹ (x₁ × y₁ ⊹ x₂ × y₂ ⊹ (x₁ × z₁ ⊹ x₂ × z₂))) (≡.symm(ℕ.*.over+.distrL x₁ y₂ z₂))(≡.symm(ℕ.*.over+.distrL x₂ y₁ z₁))⟩
                x₁ × (y₂ ⊹ z₂) ⊹ x₂ × (y₁ ⊹ z₁) ⊹ (x₁ × y₁ ⊹ x₂ × y₂ ⊹ (x₁ × z₁ ⊹ x₂ × z₂))
            ∎

    assoc : (x y z : ℤ) → x * y * z ≅ x * (y * z)
    assoc (x₁ -− x₂) (y₁ -− y₂) (z₁ -− z₂) = 
            (x₁ × y₁ ⊹ x₂ × y₂) × z₁ ⊹ (x₁ × y₂ ⊹ x₂ × y₁) × z₂ ⊹ (x₁ × (y₁ × z₂ ⊹ y₂ × z₁) ⊹ x₂ × (y₁ × z₁ ⊹ y₂ × z₂))
        ≡⟨ ≡.cong4 (λ a b c d → a ⊹ b ⊹ (c ⊹ d))
                (ℕ.*.over+.distrR (x₁ × y₁) (x₂ × y₂) z₁ ) (ℕ.*.over+.distrR (x₁ × y₂) (x₂ × y₁) z₂ )
                (ℕ.*.over+.distrL x₁ (y₁ × z₂) (y₂ × z₁) ) (ℕ.*.over+.distrL x₂ (y₁ × z₁) (y₂ × z₂) ) ⟩ 
            x₁ × y₁ × z₁ ⊹ x₂ × y₂ × z₁ ⊹ (x₁ × y₂ × z₂ ⊹ x₂ × y₁ × z₂) ⊹ (x₁ × (y₁ × z₂) ⊹ x₁ × (y₂ × z₁) ⊹ (x₂ × (y₁ × z₁) ⊹ x₂ × (y₂ × z₂)))
        ≡⟨ ≡.cong8 (λ a b c d e f g h → a ⊹ b ⊹ (c ⊹ d) ⊹ (e ⊹ f ⊹ (g ⊹ h)))
                (ℕ.*.assoc x₁ y₁ z₁) (ℕ.*.assoc x₂ y₂ z₁) (ℕ.*.assoc x₁ y₂ z₂) (ℕ.*.assoc x₂ y₁ z₂)
                (≡.symm $ ℕ.*.assoc x₁ y₁ z₂) (≡.symm $ ℕ.*.assoc x₁ y₂ z₁) (≡.symm $ ℕ.*.assoc x₂ y₁ z₁) (≡.symm $ ℕ.*.assoc x₂ y₂ z₂)⟩
            x₁ × (y₁ × z₁) ⊹ x₂ × (y₂ × z₁) ⊹ (x₁ × (y₂ × z₂) ⊹ x₂ × (y₁ × z₂)) ⊹ (x₁ × y₁ × z₂ ⊹ x₁ × y₂ × z₁ ⊹ (x₂ × y₁ × z₁ ⊹ x₂ × y₂ × z₂))
        ≡⟨ assoc∀l _⊹_ (x₁ × (y₁ × z₁) ◍ x₂ × (y₂ × z₁) ◌ (x₁ × (y₂ × z₂) ◍ x₂ × (y₁ × z₂)) ◌ (x₁ × y₁ × z₂ ◍ x₁ × y₂ × z₁ ◌ (x₂ × y₁ × z₁ ◍ x₂ × y₂ × z₂))) ⟩
            x₁ × (y₁ × z₁) ⊹ x₂ × (y₂ × z₁) ⊹ x₁ × (y₂ × z₂) ⊹ x₂ × (y₁ × z₂) ⊹ x₁ × y₁ × z₂ ⊹ x₁ × y₂ × z₁ ⊹ x₂ × y₁ × z₁ ⊹ x₂ × y₂ × z₂
        ≡⟨ (λ u → u ⊹ x₂ × (y₂ × z₁) ⊹ x₁ × (y₂ × z₂) ⊹ x₂ × (y₁ × z₂) ⊹ x₁ × y₁ × z₂ ⊹ x₁ × y₂ × z₁ ⊹ x₂ × y₁ × z₁ ⊹ x₂ × y₂ × z₂) ◈ ℕ.+.comm (x₁ × (y₁ × z₁)) 0 ⟩
            0 ⊹ x₁ × (y₁ × z₁) ⊹ x₂ × (y₂ × z₁) ⊹ x₁ × (y₂ × z₂) ⊹ x₂ × (y₁ × z₂) ⊹ x₁ × y₁ × z₂ ⊹ x₁ × y₂ × z₁ ⊹ x₂ × y₁ × z₁ ⊹ x₂ × y₂ × z₂
        ≡⟨ comm∀i _⊹_ {8} [ [ ⑴ , ⑸ ] , [ ⑵ , ⑻ ] , [ ⑶ , ⑹ ] , [ ⑷ , ⑺ ] ] 
                [ x₁ × (y₁ × z₁) , x₂ × (y₂ × z₁) , x₁ × (y₂ × z₂) , x₂ × (y₁ × z₂) , x₁ × y₁ × z₂ , x₁ × y₂ × z₁ , x₂ × y₁ × z₁ , x₂ × y₂ × z₂ ] ⟩
            0 ⊹ x₁ × y₁ × z₂ ⊹ x₂ × y₂ × z₂ ⊹ x₁ × y₂ × z₁ ⊹ x₂ × y₁ × z₁ ⊹ x₁ × (y₁ × z₁) ⊹ x₁ × (y₂ × z₂) ⊹ x₂ × (y₁ × z₂) ⊹ x₂ × (y₂ × z₁)
        ≡⟨ (λ u → u ⊹ x₂ × y₂ × z₂ ⊹ x₁ × y₂ × z₁ ⊹ x₂ × y₁ × z₁ ⊹ x₁ × (y₁ × z₁) ⊹ x₁ × (y₂ × z₂) ⊹ x₂ × (y₁ × z₂) ⊹ x₂ × (y₂ × z₁)) ◈ ℕ.+.comm 0 (x₁ × y₁ × z₂) ⟩
            x₁ × y₁ × z₂ ⊹ x₂ × y₂ × z₂ ⊹ x₁ × y₂ × z₁ ⊹ x₂ × y₁ × z₁ ⊹ x₁ × (y₁ × z₁) ⊹ x₁ × (y₂ × z₂) ⊹ x₂ × (y₁ × z₂) ⊹ x₂ × (y₂ × z₁)
        ≡⟨' assoc∀l _⊹_ ((x₁ × y₁ × z₂ ◍ x₂ × y₂ × z₂) ◌ (x₁ × y₂ × z₁ ◍ x₂ × y₁ × z₁) ◌ ((x₁ × (y₁ × z₁) ◍ x₁ × (y₂ × z₂)) ◌ (x₂ × (y₁ × z₂) ◍ x₂ × (y₂ × z₁))))⟩ 
            x₁ × y₁ × z₂ ⊹ x₂ × y₂ × z₂ ⊹ (x₁ × y₂ × z₁ ⊹ x₂ × y₁ × z₁) ⊹ (x₁ × (y₁ × z₁) ⊹ x₁ × (y₂ × z₂) ⊹ (x₂ × (y₁ × z₂) ⊹ x₂ × (y₂ × z₁)))
        ≡⟨ ≡.cong4 (λ a b c d → a ⊹ b ⊹ (c ⊹ d)) 
                (≡.symm $ ℕ.*.over+.distrR (x₁ × y₁) (x₂ × y₂) z₂ ) (≡.symm $ ℕ.*.over+.distrR (x₁ × y₂) (x₂ × y₁) z₁ )
                (≡.symm $ ℕ.*.over+.distrL x₁ (y₁ × z₁) (y₂ × z₂) ) (≡.symm $ ℕ.*.over+.distrL x₂ (y₁ × z₂) (y₂ × z₁) ) ⟩
            (x₁ × y₁ ⊹ x₂ × y₂) × z₂ ⊹ (x₁ × y₂ ⊹ x₂ × y₁) × z₁ ⊹ (x₁ × (y₁ × z₁ ⊹ y₂ × z₂) ⊹ x₂ × (y₁ × z₂ ⊹ y₂ × z₁))
        ∎

    instance
        *-Comm : Comm _*_
        Comm.comm *-Comm = comm

        *-Assoc : Assoc _*_
        Assoc.assoc *-Assoc = assoc

        *-Iden : Iden {_≃_ = _≅_} _*_
        Iden.ε *-Iden = 1 -− 0
        Iden.idenL *-Iden (x₁ -− x₂) rewrite ℕ.*.comm 1 x₁ | ℕ.*.comm 1 x₂ | ℕ.*.comm 0 x₁ | ℕ.*.comm 0 x₂ | ℕ.+.comm 0 x₁ | ℕ.+.comm 0 x₂ = ℕ.+.comm x₁ x₂
        Iden.idenR *-Iden (x₁ -− x₂) rewrite ℕ.+.comm 0 x₁ | ℕ.+.comm 0 (0 ⊹ x₂) | ℕ.+.comm 0 x₂ = ℕ.+.comm x₁ x₂

        *-Monoid : Monoid _*_
        Monoid.-Iden *-Monoid = *-Iden 