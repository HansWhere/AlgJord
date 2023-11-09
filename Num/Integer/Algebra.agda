module Num.Integer.Algebra where 
open import Control.Function.Util hiding (id)
open import Num.Natural.Algebra as ℕ using () renaming (_+_ to _⊹_; _*_ to _×_)
open import Num.Integer.Definition as ℤ renaming (_,_ to _,,_) 
open import Num.Natural.Definition using (ℕ; 1≠0)
open import Algebra.Operator.Binary.Property using (Comm; Assoc; Distr; Iden; Cong; Free; assoc∀l; _◌_; _◍_; _◐_; _◑_)
open import Algebra.Operator.Binary.Monoid using (Monoid; comm∀i)
open import Control.List.Definition
open import Control.Finite.Definition
open import Relation.Equality as ≡ using (_≡_; _≡⟨_⟩_; _≡⟨'_⟩_; _≡⟨⟩_; _∎; _◈_; _≡➤_)
open import Relation.Equivalance

infixl 60 _+_ 
_+_ : ℤ → ℤ → ℤ
(x1 − x2) + (y1 − y2) = (x1 ⊹ y1) − (x2 ⊹ y2) 

module + where
    comm : (x y : ℤ) → x + y ≅ y + x 
    comm (x1 − x2) (y1 − y2) = ℕ.+.comm (x1 ⊹ y1) (y2 ⊹ x2) ≡➤ ≡.cong2 _⊹_ (ℕ.+.comm y2 x2) (ℕ.+.comm x1 y1)

    id : ℤ
    id = 0z

    idenL : (x : ℤ) → id + x ≅ x
    idenL (x1 − x2) rewrite ℕ.+.comm 0 x1 | ℕ.+.comm 0 x2 = ℕ.+.comm x1 x2

    idenR : (x : ℤ) → x + id ≅ x
    idenR (x1 − x2) = ℕ.+.comm x1 x2

    assoc : (x y z : ℤ) → x + y + z ≅ x + (y + z)
    assoc (x1 − x2) (y1 − y2) (z1 − z2) = 
            (x1 ⊹ y1 ⊹ z1) ⊹ (x2 ⊹ (y2 ⊹ z2))
        ≡⟨ ℕ.+.comm (x1 ⊹ y1 ⊹ z1) (x2 ⊹ (y2 ⊹ z2)) ⟩ 
            (x2 ⊹ (y2 ⊹ z2)) ⊹ (x1 ⊹ y1 ⊹ z1)
        ≡⟨ ≡.cong2 _⊹_ (≡.symm (ℕ.+.assoc x2 y2 z2)) (ℕ.+.assoc x1 y1 z1) ⟩
            x2 ⊹ y2 ⊹ z2 ⊹ (x1 ⊹ (y1 ⊹ z1))
        ∎

    inv : ℤ → ℤ
    inv (x1 − x2) = x2 − x1

    infixl 60 _-_
    _-_ : ℤ → ℤ → ℤ
    (x1 − x2) - (y1 − y2) = (x1 ⊹ y2) − (y1 ⊹ x2)

    invsL : (x : ℤ) → inv x + x ≅ id
    invsL (x1 − x2) = ℕ.+.comm x2 x1

    invsR : (x : ℤ) → x + inv x ≅ id
    invsR (x1 − x2) = ℕ.+.comm x1 x2

    cong : {a b c d : ℤ} → (a ≅ b) → (c ≅ d) → ((a + c) ≅ (b + d))
    cong {a1 − a2} {b1 − b2} {c1 − c2} {d1 − d2} a≅b c≅d 
        rewrite ≡.symm $ ℕ.+.assoc (a1 ⊹ c1) b2 d2 | ≡.symm $ ℕ.+.assoc (a2 ⊹ c2) b1 d1 
        | ℕ.+.assoc a1 c1 b2 | ℕ.+.assoc a2 c2 b1 
        | ℕ.+.comm c1 b2 | ℕ.+.comm c2 b1
        | ≡.symm $ ℕ.+.assoc a1 b2 c1 | ≡.symm $ ℕ.+.assoc a2 b1 c2 
        | ℕ.+.assoc (a1 ⊹ b2) c1 d2 | ℕ.+.assoc (a2 ⊹ b1) c2 d1
        | a≅b | c≅d = ≡.refl

    module cong where
        -inv : {x y : ℤ} → x ≅ y → inv x ≅ inv y
        -inv {x1 − x2} {y1 − y2} x≅y = ≡.symm x≅y

    canc : (x y c : ℤ) → x + c ≅ y + c → x ≅ y
    canc (x1 − x2) (y1 − y2) (c1 − c2) eq rewrite 
        ≡.symm $ ℕ.+.assoc (x1 ⊹ c1) y2 c2 | ≡.symm $ ℕ.+.assoc (x2 ⊹ c2) y1 c1 | ℕ.+.comm x1 0 | ℕ.+.comm x2 0 |
        comm∀i _⊹_ {4} [ [ ⑵ , ⑶ ] ] [ x1 , c1 , y2 , c2 ] | comm∀i _⊹_ {4} [ [ ⑵ , ⑶ , ⑷ ] ] [ x2 , c2 , y1 , c1 ] |
        ℕ.+.assoc (0 ⊹ x1 ⊹ y2) c1 c2 | ℕ.+.assoc (0 ⊹ x2 ⊹ y1) c1 c2
        = ℕ.+.canc (0 ⊹ x1 ⊹ y2) (0 ⊹ x2 ⊹ y1) (c1 ⊹ c2) eq

    instance
        +-Comm : Comm _+_
        Comm.comm +-Comm = comm

        +-Assoc : Assoc _+_
        Assoc.assoc +-Assoc = assoc

        +-Iden : Iden {_≃_ = _≅_} _+_
        Iden.id +-Iden = 0z
        Iden.idenL +-Iden (x1 − x2) rewrite ℕ.+.comm 0 x1 | ℕ.+.comm 0 x2 = ℕ.+.comm x1 x2
        Iden.idenR +-Iden (x1 − x2) = ℕ.+.comm x1 x2

        +-Monoid : Monoid _+_
        Monoid.-Iden +-Monoid = +-Iden 

infixl 70 _*_ 
_*_ : ℤ → ℤ → ℤ
(x1 − x2) * (y1 − y2) = (x1 × y1 ⊹ x2 × y2) − (x1 × y2 ⊹ x2 × y1)

module * where
    comm : (x y : ℤ) → x * y ≅ y * x 
    comm (x1 − x2) (y1 − y2) = 
            (x1 × y1 ⊹ x2 × y2) ⊹ (y1 × x2 ⊹ y2 × x1)
        ≡⟨ ℕ.+.comm (x1 × y1 ⊹ x2 × y2) (y1 × x2 ⊹ y2 × x1) ⟩
            (y1 × x2 ⊹ y2 × x1) ⊹ (x1 × y1 ⊹ x2 × y2)
        ≡⟨ (λ u → u ⊹ (x1 × y1 ⊹ x2 × y2)) ◈ (ℕ.+.comm (y1 × x2) (y2 × x1)) ⟩
            (y2 × x1 ⊹ y1 × x2) ⊹ (x1 × y1 ⊹ x2 × y2)
        ≡⟨ ≡.cong4 (λ a b c d → (a ⊹ b) ⊹ (c ⊹ d)) (ℕ.*.comm y2 x1) (ℕ.*.comm y1 x2) (ℕ.*.comm x1 y1) (ℕ.*.comm x2 y2) ⟩
            (x1 × y2 ⊹ x2 × y1) ⊹ (y1 × x1 ⊹ y2 × x2)
        ∎

    id : ℤ
    id = 1 − 0

    idenL : (x : ℤ) → id * x ≅ x
    idenL (x1 − x2) rewrite ℕ.*.comm 1 x1 | ℕ.*.comm 0 x2 | ℕ.*.comm 1 x2 | ℕ.*.comm 0 x1
        | ℕ.+.comm 0 x1 | ℕ.+.comm 0 x2 = ℕ.+.comm x1 x2

    idenR : (x : ℤ) → x * id ≅ x
    idenR (x1 − x2) rewrite ℕ.+.comm 0 x1 | ℕ.+.comm 0 x2 | ℕ.+.comm 0 x2 = ℕ.+.comm x1 x2 

    zero : ℤ
    zero = 0z

    zeroL : (x : ℤ) → zero * x ≅ zero
    zeroL x@(x1 − x2) = comm zero x

    zeroR : (x : ℤ) → x * zero ≅ zero
    zeroR x@(x1 − x2) = ≡.refl

    private 
        cong-c : {a b : ℤ} (c : ℤ) → (a ≅ b) → ((a * c) ≅ (b * c))
        cong-c {a1 − a2} {b1 − b2} (c1 − c2) a≅b 
            rewrite ≡.symm $ ℕ.+.assoc (a1 × c1 ⊹ a2 × c2) (b1 × c2) (b2 × c1)
            | ≡.symm $ ℕ.+.assoc (a1 × c2 ⊹ a2 × c1) (b1 × c1) (b2 × c2)
            | ℕ.+.assoc (a1 × c1) (a2 × c2) (b1 × c2)
            | ℕ.+.assoc (a1 × c2) (a2 × c1) (b1 × c1)
            | ℕ.+.comm (a1 × c1) (a2 × c2 ⊹ b1 × c2)
            | ℕ.+.comm (a1 × c2) (a2 × c1 ⊹ b1 × c1)
            | ℕ.+.assoc (a2 × c2 ⊹ b1 × c2) (a1 × c1) (b2 × c1)
            | ℕ.+.assoc (a2 × c1 ⊹ b1 × c1) (a1 × c2) (b2 × c2)
            | ≡.symm $ ℕ.*.over+.distrR a2 b1 c2
            | ≡.symm $ ℕ.*.over+.distrR a1 b2 c1
            | ≡.symm $ ℕ.*.over+.distrR a2 b1 c1 
            | ≡.symm $ ℕ.*.over+.distrR a1 b2 c2
            | a≅b
            = ℕ.+.comm ((a2 ⊹ b1) × c2) ((a2 ⊹ b1) × c1)

    cong : {a b c d : ℤ} → (a ≅ b) → (c ≅ d) → ((a * c) ≅ (b * d))
    cong {a} {b} {c} {d} a≅b c≅d = 
            a * c
        ≃⟨ cong-c c a≅b ⟩ 
            b * c
        ≃⟨ comm b c ⟩
            c * b
        ≃⟨ cong-c b c≅d ⟩
            d * b
        ≃⟨ comm d b ⟩
            b * d
        □

    module cong where

    module over+ where
        distrL : (x y z : ℤ) → x * (y + z) ≅ x * y + x * z 
        distrL (x1 − x2) (y1 − y2) (z1 − z2) = 
                x1 × (y1 ⊹ z1) ⊹ x2 × (y2 ⊹ z2) ⊹ (x1 × y2 ⊹ x2 × y1 ⊹ (x1 × z2 ⊹ x2 × z1))
            ≡⟨ ≡.cong2 (λ a b → a ⊹ b ⊹ (x1 × y2 ⊹ x2 × y1 ⊹ (x1 × z2 ⊹ x2 × z1))) (ℕ.*.over+.distrL x1 y1 z1) (ℕ.*.over+.distrL x2 y2 z2)⟩
                x1 × y1 ⊹ x1 × z1 ⊹ (x2 × y2 ⊹ x2 × z2) ⊹ (x1 × y2 ⊹ x2 × y1 ⊹ (x1 × z2 ⊹ x2 × z1))
            ≡⟨ assoc∀l _⊹_ ((x1 × y1 ◍ x1 × z1) ◌ (x2 × y2 ◍ x2 × z2) ◌ ((x1 × y2 ◍ x2 × y1) ◌ (x1 × z2 ◍ x2 × z1)))⟩
                x1 × y1 ⊹ x1 × z1 ⊹ x2 × y2 ⊹ x2 × z2 ⊹ x1 × y2 ⊹ x2 × y1 ⊹ x1 × z2 ⊹ x2 × z1
            ≡⟨ (λ u → u ⊹ x1 × z1 ⊹ x2 × y2 ⊹ x2 × z2 ⊹ x1 × y2 ⊹ x2 × y1 ⊹ x1 × z2 ⊹ x2 × z1) ◈ ℕ.+.comm (x1 × y1) 0 ⟩
                0 ⊹ x1 × y1 ⊹ x1 × z1 ⊹ x2 × y2 ⊹ x2 × z2 ⊹ x1 × y2 ⊹ x2 × y1 ⊹ x1 × z2 ⊹ x2 × z1
            ≡⟨ comm∀i _⊹_ {8} [ [ ⑴ , ⑸ ] , [ ⑵ , ⑺ ] , [ ⑶ , ⑹ ] , [ ⑷ , ⑻ ] ] 
                    [ x1 × y1 , x1 × z1 , x2 × y2 , x2 × z2 , x1 × y2 , x2 × y1 , x1 × z2 , x2 × z1 ] ⟩
                0 ⊹ x1 × y2 ⊹ x1 × z2 ⊹ x2 × y1 ⊹ x2 × z1 ⊹ x1 × y1 ⊹ x2 × y2 ⊹ x1 × z1 ⊹ x2 × z2
            ≡⟨ (λ u → u ⊹ x1 × z2 ⊹ x2 × y1 ⊹ x2 × z1 ⊹ x1 × y1 ⊹ x2 × y2 ⊹ x1 × z1 ⊹ x2 × z2) ◈ ℕ.+.comm 0 (x1 × y2)⟩
                x1 × y2 ⊹ x1 × z2 ⊹ x2 × y1 ⊹ x2 × z1 ⊹ x1 × y1 ⊹ x2 × y2 ⊹ x1 × z1 ⊹ x2 × z2
            ≡⟨' assoc∀l _⊹_ ((x1 × y2 ◍ x1 × z2) ◌ (x2 × y1 ◍ x2 × z1) ◌ ((x1 × y1 ◍ x2 × y2) ◌ (x1 × z1 ◍ x2 × z2)))⟩
                (x1 × y2 ⊹ x1 × z2) ⊹ (x2 × y1 ⊹ x2 × z1) ⊹ (x1 × y1 ⊹ x2 × y2 ⊹ (x1 × z1 ⊹ x2 × z2))
            ≡⟨ ≡.cong2 (λ a b → a ⊹ b ⊹ (x1 × y1 ⊹ x2 × y2 ⊹ (x1 × z1 ⊹ x2 × z2))) (≡.symm(ℕ.*.over+.distrL x1 y2 z2))(≡.symm(ℕ.*.over+.distrL x2 y1 z1))⟩
                x1 × (y2 ⊹ z2) ⊹ x2 × (y1 ⊹ z1) ⊹ (x1 × y1 ⊹ x2 × y2 ⊹ (x1 × z1 ⊹ x2 × z2))
            ∎

        distrR : (x y z : ℤ) → (x + y) * z ≅ x * z + y * z
        distrR x y z = 
                (x + y) * z
            ≃⟨ comm (x + y) z ⟩
                z * (x + y)
            ≃⟨ distrL z x y ⟩
                z * x + z * y
            ≃⟨ +.cong (comm z x) (comm z y) ⟩
                x * z + y * z
            □

        neg-means-*−1 : (x : ℤ) → (+.inv x) ≅ x * +.inv id
        neg-means-*−1 (x1 − x2) rewrite ℕ.+.comm 0 x1 | ℕ.+.comm 0 x2 | ℕ.+.comm 0 x2 = ℕ.+.comm x2 x1 

    assoc : (x y z : ℤ) → x * y * z ≅ x * (y * z)
    assoc (x1 − x2) (y1 − y2) (z1 − z2) = 
            (x1 × y1 ⊹ x2 × y2) × z1 ⊹ (x1 × y2 ⊹ x2 × y1) × z2 ⊹ (x1 × (y1 × z2 ⊹ y2 × z1) ⊹ x2 × (y1 × z1 ⊹ y2 × z2))
        ≡⟨ ≡.cong4 (λ a b c d → a ⊹ b ⊹ (c ⊹ d))
                (ℕ.*.over+.distrR (x1 × y1) (x2 × y2) z1 ) (ℕ.*.over+.distrR (x1 × y2) (x2 × y1) z2 )
                (ℕ.*.over+.distrL x1 (y1 × z2) (y2 × z1) ) (ℕ.*.over+.distrL x2 (y1 × z1) (y2 × z2) ) ⟩ 
            x1 × y1 × z1 ⊹ x2 × y2 × z1 ⊹ (x1 × y2 × z2 ⊹ x2 × y1 × z2) ⊹ (x1 × (y1 × z2) ⊹ x1 × (y2 × z1) ⊹ (x2 × (y1 × z1) ⊹ x2 × (y2 × z2)))
        ≡⟨ ≡.cong8 (λ a b c d e f g h → a ⊹ b ⊹ (c ⊹ d) ⊹ (e ⊹ f ⊹ (g ⊹ h)))
                (ℕ.*.assoc x1 y1 z1) (ℕ.*.assoc x2 y2 z1) (ℕ.*.assoc x1 y2 z2) (ℕ.*.assoc x2 y1 z2)
                (≡.symm $ ℕ.*.assoc x1 y1 z2) (≡.symm $ ℕ.*.assoc x1 y2 z1) (≡.symm $ ℕ.*.assoc x2 y1 z1) (≡.symm $ ℕ.*.assoc x2 y2 z2)⟩
            x1 × (y1 × z1) ⊹ x2 × (y2 × z1) ⊹ (x1 × (y2 × z2) ⊹ x2 × (y1 × z2)) ⊹ (x1 × y1 × z2 ⊹ x1 × y2 × z1 ⊹ (x2 × y1 × z1 ⊹ x2 × y2 × z2))
        ≡⟨ assoc∀l _⊹_ (x1 × (y1 × z1) ◍ x2 × (y2 × z1) ◌ (x1 × (y2 × z2) ◍ x2 × (y1 × z2)) ◌ (x1 × y1 × z2 ◍ x1 × y2 × z1 ◌ (x2 × y1 × z1 ◍ x2 × y2 × z2))) ⟩
            x1 × (y1 × z1) ⊹ x2 × (y2 × z1) ⊹ x1 × (y2 × z2) ⊹ x2 × (y1 × z2) ⊹ x1 × y1 × z2 ⊹ x1 × y2 × z1 ⊹ x2 × y1 × z1 ⊹ x2 × y2 × z2
        ≡⟨ (λ u → u ⊹ x2 × (y2 × z1) ⊹ x1 × (y2 × z2) ⊹ x2 × (y1 × z2) ⊹ x1 × y1 × z2 ⊹ x1 × y2 × z1 ⊹ x2 × y1 × z1 ⊹ x2 × y2 × z2) ◈ ℕ.+.comm (x1 × (y1 × z1)) 0 ⟩
            0 ⊹ x1 × (y1 × z1) ⊹ x2 × (y2 × z1) ⊹ x1 × (y2 × z2) ⊹ x2 × (y1 × z2) ⊹ x1 × y1 × z2 ⊹ x1 × y2 × z1 ⊹ x2 × y1 × z1 ⊹ x2 × y2 × z2
        ≡⟨ comm∀i _⊹_ {8} [ [ ⑴ , ⑸ ] , [ ⑵ , ⑻ ] , [ ⑶ , ⑹ ] , [ ⑷ , ⑺ ] ] 
                [ x1 × (y1 × z1) , x2 × (y2 × z1) , x1 × (y2 × z2) , x2 × (y1 × z2) , x1 × y1 × z2 , x1 × y2 × z1 , x2 × y1 × z1 , x2 × y2 × z2 ] ⟩
            0 ⊹ x1 × y1 × z2 ⊹ x2 × y2 × z2 ⊹ x1 × y2 × z1 ⊹ x2 × y1 × z1 ⊹ x1 × (y1 × z1) ⊹ x1 × (y2 × z2) ⊹ x2 × (y1 × z2) ⊹ x2 × (y2 × z1)
        ≡⟨ (λ u → u ⊹ x2 × y2 × z2 ⊹ x1 × y2 × z1 ⊹ x2 × y1 × z1 ⊹ x1 × (y1 × z1) ⊹ x1 × (y2 × z2) ⊹ x2 × (y1 × z2) ⊹ x2 × (y2 × z1)) ◈ ℕ.+.comm 0 (x1 × y1 × z2) ⟩
            x1 × y1 × z2 ⊹ x2 × y2 × z2 ⊹ x1 × y2 × z1 ⊹ x2 × y1 × z1 ⊹ x1 × (y1 × z1) ⊹ x1 × (y2 × z2) ⊹ x2 × (y1 × z2) ⊹ x2 × (y2 × z1)
        ≡⟨' assoc∀l _⊹_ ((x1 × y1 × z2 ◍ x2 × y2 × z2) ◌ (x1 × y2 × z1 ◍ x2 × y1 × z1) ◌ ((x1 × (y1 × z1) ◍ x1 × (y2 × z2)) ◌ (x2 × (y1 × z2) ◍ x2 × (y2 × z1))))⟩ 
            x1 × y1 × z2 ⊹ x2 × y2 × z2 ⊹ (x1 × y2 × z1 ⊹ x2 × y1 × z1) ⊹ (x1 × (y1 × z1) ⊹ x1 × (y2 × z2) ⊹ (x2 × (y1 × z2) ⊹ x2 × (y2 × z1)))
        ≡⟨ ≡.cong4 (λ a b c d → a ⊹ b ⊹ (c ⊹ d)) 
                (≡.symm $ ℕ.*.over+.distrR (x1 × y1) (x2 × y2) z2 ) (≡.symm $ ℕ.*.over+.distrR (x1 × y2) (x2 × y1) z1 )
                (≡.symm $ ℕ.*.over+.distrL x1 (y1 × z1) (y2 × z2) ) (≡.symm $ ℕ.*.over+.distrL x2 (y1 × z2) (y2 × z1) ) ⟩
            (x1 × y1 ⊹ x2 × y2) × z2 ⊹ (x1 × y2 ⊹ x2 × y1) × z1 ⊹ (x1 × (y1 × z1 ⊹ y2 × z2) ⊹ x2 × (y1 × z2 ⊹ y2 × z1))
        ∎

    no-0divisor : (x y : ℤ) → x * y ≅ 0z → y ≇ 0z → x ≅ 0z
    no-0divisor x y x*y≡0 y≠0 with trichotomy y but y≠0 | trichotomy x
    ... | _ | rgt x≅0 = x≅0
    ... | lft (n :, y≡n+1) | lft (lft (m :, x≡m+1)) = 
        ecq $ 1≠0 $ ≡.symm $ ℕ.*.comm n 0 ≡➤ ℕ.+.comm (0 × n) 0 ≡➤ ℕ.+.comm (0 ⊹ 0 × n) 0 ≡➤ ℤ.≅.trans (ℤ.≅.symm x*y≡0) (cong x≡m+1 y≡n+1)
    ... | lft (n :, y≡n+1) | lft (rgt (m :, x≡-m-1)) = 
        ecq $ 1≠0 $ ℤ.≅.trans (ℤ.≅.symm x*y≡0) (cong x≡-m-1 y≡n+1) ≡➤ ℕ.+.comm 0 (0 × n) ≡➤ ℕ.*.comm 0 n
    ... | rgt (n :, y≡-n-1) | lft (lft (m :, x≡m+1)) = 
        ecq $ 1≠0 $ ℤ.≅.trans (ℤ.≅.symm x*y≡0) (cong x≡m+1 y≡-n-1) ≡➤ ℕ.+.comm 0 (0 ⊹ 0 × n) ≡➤ ℕ.+.comm 0 (0 × n) ≡➤ ℕ.*.comm 0 n
    ... | rgt (n :, y≡-n-1) | lft (rgt (m :, x≡-m-1)) = 
        ecq $ 1≠0 $ ≡.symm $ ℕ.*.comm n 0 ≡➤ ℕ.+.comm (0 × n) 0 ≡➤ ℤ.≅.trans (ℤ.≅.symm x*y≡0) (cong x≡-m-1 y≡-n-1)

    -- no-0divisor' : (x y : ℤ) → x ≇ 0z → y ≇ 0z → x * y ≇ 0z
    -- no-0divisor' x y x≇0 y≇0 x*y≅0 = x≇0 (no-0divisor x y x*y≅0 y≇0)

    canc : (x y c : ℤ) → c ≇ 0z → x * c ≅ y * c → x ≅ y
    canc x y c c≠0 xc≅yc = x
        ≃⟨ symm $ +.idenR x ⟩
            x + +.id
        ≃⟨ +.cong refl (symm $ +.invsL y) ⟩ 
            x + (+.inv y + y)
        ≃⟨ symm $ +.assoc x (+.inv y) y ⟩ 
            x + +.inv y + y
        ≃⟨ +.cong (no-0divisor (x + +.inv y) c eq1 c≠0) (refl {x = y}) ⟩
            0z + y
        ≃⟨ +.idenL y ⟩
            y
        □
        where eq1 = (x + +.inv y) * c
                ≃⟨ over+.distrR x (+.inv y) c ⟩
                    x * c + +.inv y * c
                ≃⟨ +.cong xc≅yc refl ⟩
                    y * c + +.inv y * c
                ≃⟨ symm $ over+.distrR y (+.inv y) c ⟩
                    (y + +.inv y) * c
                ≃⟨ cong (+.invsR y) refl ⟩
                    zero * c
                ≃⟨ zeroL c ⟩
                    zero
                □

    instance
        *-Comm : Comm _*_
        Comm.comm *-Comm = comm

        *-Assoc : Assoc _*_
        Assoc.assoc *-Assoc = assoc

        *-Iden : Iden {_≃_ = _≅_} _*_
        Iden.id *-Iden = 1 − 0
        Iden.idenL *-Iden (x1 − x2) rewrite ℕ.*.comm 1 x1 | ℕ.*.comm 1 x2 | ℕ.*.comm 0 x1 | ℕ.*.comm 0 x2 | ℕ.+.comm 0 x1 | ℕ.+.comm 0 x2 = ℕ.+.comm x1 x2
        Iden.idenR *-Iden (x1 − x2) rewrite ℕ.+.comm 0 x1 | ℕ.+.comm 0 (0 ⊹ x2) | ℕ.+.comm 0 x2 = ℕ.+.comm x1 x2

        *-Monoid : Monoid _*_
        Monoid.-Iden *-Monoid = *-Iden 