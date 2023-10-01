module Num.Natural.Algebra where
open import Control.Function.Util hiding (id)
open import Relation.Equality as ≡ 
open import Num.Natural.Definition as ℕ using (ℕ; succ; zero; 1≠0)
open import Logic.Connective using (_∧_; _,_)
open import Algebra.Operator.Binary.Property using (Comm; Assoc; Distr; Iden; Cong)
open import Algebra.Operator.Binary.Monoid using (Monoid)
open import Logic.Absurdum

module + where
    infixl 60 _+_
    _+_ : ℕ → ℕ → ℕ
    x + zero = x
    x + succ y = succ (x + y)
    {-# BUILTIN NATPLUS _+_ #-}

    left-iden : (x : ℕ) → zero + x ≡ x
    left-iden zero = ≡.refl
    left-iden (succ x) = 
            zero + (succ x)
        ≡⟨⟩ 
            succ (zero + x)
        ≡⟨ succ ◈ left-iden x ⟩ 
            succ x 
        ∎
    left-succ : (x y : ℕ) → succ x + y ≡ succ (x + y)
    left-succ x zero = ≡.refl
    left-succ x (succ y) = 
            succ x + succ y
        ≡⟨⟩ 
            succ (succ x + y)
        ≡⟨ succ ◈ left-succ x y ⟩ 
            succ (succ (x + y))
        ≡⟨⟩ 
            succ (x + succ y)
        ∎

    comm : (x y : ℕ) → x + y ≡ y + x 
    comm zero y = left-iden y 
    comm (succ x) y = 
            succ x + y 
        ≡⟨ left-succ x y ⟩ 
            succ (x + y)
        ≡⟨ succ ◈ comm x y ⟩ 
            succ (y + x)
        ≡⟨⟩
            y + succ x 
        ∎

    assoc : (x y z : ℕ) → x + y + z ≡ x + (y + z)
    assoc x y zero = ≡.refl
    assoc x y (succ z) = 
            x + y + succ z
        ≡⟨⟩ 
            succ (x + y + z)
        ≡⟨ succ ◈ assoc x y z ⟩ 
            succ (x + (y + z))
        ≡⟨⟩ 
            x + (y + succ z)
        ∎

    instance
        +over≡-Cong : Cong _≡_ _+_
        Cong.cong +over≡-Cong = ≡.cong2 _+_

        +-Comm : Comm _+_
        Comm.comm +-Comm = comm

        +-Assoc : Assoc _+_
        Assoc.assoc +-Assoc = assoc

        +-Iden : Iden _+_ 
        Iden.id +-Iden = 0
        Iden.idenL +-Iden = left-iden
        Iden.idenR +-Iden x = ≡.refl

        +-Monoid : Monoid _+_
        Monoid.-Iden +-Monoid = +-Iden

    infixl 60 _∸_
    _∸_ : ℕ → ℕ → ℕ
    x ∸ zero = x 
    zero ∸ succ x = zero 
    succ x ∸ succ y = x ∸ y 

    pred : ℕ → ℕ
    pred zero = zero 
    pred (succ x) = x 

    canc : (x y c : ℕ) → x + c ≡ y + c → x ≡ y
    canc x y zero x+c≡y+c = x+c≡y+c
    canc x y (succ c) x+c≡y+c = canc x y c (pred ◈ x+c≡y+c)

module * where
    open + using (_+_)
    infixl 70 _*_
    _*_ : ℕ → ℕ → ℕ
    x * zero = zero 
    x * succ y = x * y + x
    {-# BUILTIN NATTIMES _*_ #-}

    private
        left-zero : (x : ℕ) → zero * x ≡ zero 
        left-zero zero = ≡.refl 
        left-zero (succ x) = 
                zero * (succ x)
            ≡⟨⟩
                zero * x + zero
            ≡⟨⟩
                zero * x 
            ≡⟨ left-zero x ⟩
                zero 
            ∎
        
        left-succ : (x y : ℕ) → succ x * y ≡ x * y + y 
        left-succ x zero = ≡.refl
        left-succ x (succ y) = 
                succ x * succ y 
            ≡⟨⟩
                succ x * y + succ x 
            ≡⟨ (λ u → u + succ x) ◈ left-succ x y ⟩
                x * y + y + succ x 
            ≡⟨ +.assoc (x * y) y (succ x) ⟩
                x * y + succ (y + x)
            ≡⟨ (λ u → x * y + succ u) ◈ +.comm y x ⟩
                x * y + succ (x + y)
            ≡⟨⟩
                x * y + (x + succ y) 
            ≡⟨ ≡.symm (+.assoc (x * y) x (succ y)) ⟩
                x * y + x + succ y 
            ≡⟨⟩
                x * succ y + succ y 
            ∎        

    comm : (x y : ℕ) → x * y ≡ y * x 
    comm zero y = left-zero y 
    comm (succ x) y = 
            succ x * y
        ≡⟨ left-succ x y ⟩
            x * y + y 
        ≡⟨ (λ u → u + y) ◈ comm x y ⟩
            y * succ x 
        ∎

    module over+ where
        distrL : (x y z : ℕ) → x * (y + z) ≡ x * y + x * z 
        distrL x y zero = ≡.refl
        distrL x y (succ z) = 
                x * (y + succ z)
            ≡⟨⟩
                x * succ (y + z)
            ≡⟨⟩
                x * (y + z) + x 
            ≡⟨ (λ u → u + x) ◈ distrL x y z ⟩
                x * y + x * z + x 
            ≡⟨ +.assoc (x * y) (x * z) x ⟩
                x * y + (x * z + x)
            ≡⟨⟩
                x * y + x * succ z 
            ∎
        distrR : (x y z : ℕ) → (x + y) * z ≡ x * z + y * z
        distrR x y z =
                (x + y) * z
            ≡⟨ comm (x + y) z ⟩
                z * (x + y)
            ≡⟨ distrL z x y ⟩
                z * x + z * y 
            ≡⟨ ≡.cong2 (λ u v → u + v) (comm z x) (comm z y) ⟩
                x * z + y * z
            ∎
        distr : (x y z : ℕ) → x * (y + z) ≡ x * y + x * z ∧ (x + y) * z ≡ x * z + y * z
        distr x y z = distrL x y z , distrR x y z 

        instance
            *over+-Distr : Distr _+_ _*_ 
            Distr.distrL *over+-Distr = distrL
            Distr.distrR *over+-Distr = distrR

    assoc : (x y z : ℕ) → x * y * z ≡ x * (y * z)
    assoc x y zero = ≡.refl
    assoc x y (succ z) = 
            x * y * succ z
        ≡⟨⟩
            x * y * z + x * y 
        ≡⟨ (λ u → u + x * y) ◈ assoc x y z ⟩
            x * (y * z) + x * y 
        ≡⟨ ≡.symm (over+.distrL x (y * z) y) ⟩
            x * (y * z + y)
        ≡⟨⟩
            x * (y * succ z)
        ∎

    no-0divisor : (x y : ℕ) → x * y ≡ 0 → ¬ y ≡ 0 → x ≡ 0
    no-0divisor 0 y _ _ = refl
    no-0divisor (succ x) 0 x*y≡0 y≠0 = ecq (y≠0 refl) 
    no-0divisor (succ x) (succ y) x*y≡0 _ = ecq (1≠0 x*y≡0) 

    canc : (x y c : ℕ) → x * succ c ≡ y * succ c → x ≡ y
    canc x 0 c x*sc≡0*sc rewrite comm 0 (succ c) = no-0divisor x (succ c) x*sc≡0*sc λ()
    canc 0 (succ y) c 0*sc=sy*sc rewrite comm 0 (succ c) = ≡.symm (no-0divisor (succ y) (succ c) (≡.symm 0*sc=sy*sc) λ())
    canc (succ x) (succ y) c sx*sc=sy*sc rewrite comm (succ x) (succ c) | comm (succ y) (succ c) =
        succ ◈ (canc x y c $ comm x (succ c) ≡➤ +.canc (succ c * x) (succ c * y) (succ c) sx*sc=sy*sc ≡➤ comm (succ c) y)
    
    instance
        *over≡-Cong : Cong _≡_ _*_
        Cong.cong *over≡-Cong = ≡.cong2 _*_

        *-Comm : Comm _*_
        Comm.comm *-Comm = comm

        *-Assoc : Assoc _*_
        Assoc.assoc *-Assoc = assoc

        *-Iden : Iden _*_ 
        Iden.id *-Iden = 1
        Iden.idenL *-Iden x = 
                1 * x
            ≡⟨ left-succ 0 x ⟩
                0 * x + x
            ≡⟨ (λ u → u + x) ◈ left-zero x ⟩ 
                0 + x
            ≡⟨ +.comm 0 x ⟩ 
                x
            ∎  
        Iden.idenR *-Iden x = +.comm 0 x

        *-Monoid : Monoid _*_
        Monoid.-Iden *-Monoid = *-Iden

