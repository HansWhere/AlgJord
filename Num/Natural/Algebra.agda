module Num.Natural.Algebra where
open import Relation.Equality as ≡ using (_≡_; _≡⟨_⟩_; _≡⟨'_⟩_; _≡⟨⟩_; _∎; _◈_)
open import Num.Natural.Definition as ℕ using (ℕ; succ; zero)
open import Logic.Connective using (_∧_; _⹁_)

module + where
    infixl 60 _+_
    _+_ : ℕ → ℕ → ℕ
    x + zero = x
    x + succ y = succ (x + y)
    {-# BUILTIN NATPLUS _+_ #-}

    private
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
    assoc x y zero = 
            x + y + zero 
        ≡⟨⟩ 
            x + y
        ≡⟨ (λ u → x + u) ◈ ≡.refl ⟩ 
            x + (y + zero) 
        ∎
    assoc x y (succ z) = 
            x + y + succ z
        ≡⟨⟩ 
            succ (x + y + z)
        ≡⟨ succ ◈ assoc x y z ⟩ 
            succ (x + (y + z))
        ≡⟨⟩ 
            x + (y + succ z)
        ∎

    infixl 60 _∸_
    _∸_ : ℕ → ℕ → ℕ
    x ∸ zero = x 
    zero ∸ x = zero 
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

    module to+ where
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
        distr x y z = distrL x y z ⹁ distrR x y z 

    assoc : (x y z : ℕ) → x * y * z ≡ x * (y * z)
    assoc x y zero = ≡.refl
    assoc x y (succ z) = 
            x * y * succ z
        ≡⟨⟩
            x * y * z + x * y 
        ≡⟨ (λ u → u + x * y) ◈ assoc x y z ⟩
            x * (y * z) + x * y 
        ≡⟨ ≡.symm (to+.distrL x (y * z) y) ⟩
            x * (y * z + y)
        ≡⟨⟩
            x * (y * succ z)
        ∎
