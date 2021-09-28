module Control.List.Definition where
open import Agda.Primitive using (Level)
open import Num.Natural.Definition using (ℕ)

private 
    variable
        ℓ ℓ' : Level

infixr 50 _::_
infixr 49 _++_ 
data List (A : Set ℓ) : Set ℓ where
    [] : List A 
    _::_ : A → List A → List A 
{-# BUILTIN LIST List #-}

length : {A : Set ℓ} → List A → ℕ
length [] = ℕ.zero
length (x :: xs) = ℕ.succ (length xs)

_++_ : {A : Set ℓ} → List A → List A → List A 
[] ++ ys = ys
x :: xs ++ ys = x :: (xs ++ ys)

index/ : {A : Set ℓ} → List A → ℕ → A → A
index/ [] n a = a
index/ (x :: xs) ℕ.zero _ = x
index/ (x :: xs) (ℕ.succ n) a = index/ xs n a

shunt : {A : Set ℓ} → List A → List A → List A
shunt [] ys = []
shunt (x :: xs) ys = shunt xs (x :: ys)

reverse : {A : Set ℓ} → List A → List A 
reverse xs = shunt xs []

[⋯_] : ℕ → List ℕ
[⋯ ℕ.zero ] = ℕ.zero :: []
[⋯ ℕ.succ x ] = [⋯ x ] ++ (ℕ.succ x :: [])

[_⋯] : ℕ → List ℕ
[ ℕ.zero ⋯] = ℕ.zero :: []
[ ℕ.succ x ⋯] = ℕ.succ x :: [ x ⋯]

[_⋯_] : ℕ → ℕ → List ℕ
[ ℕ.zero ⋯ y ] = [⋯ y ]
[ x ⋯ ℕ.zero ] = [ x ⋯]
[ ℕ.succ x ⋯ ℕ.succ y ] with [ x ⋯ ℕ.succ y ]
... | [] = []
... | x' :: xs = xs

pattern [_] z = 
    z :: []
pattern [_,_] y z = 
    y :: z :: []
pattern [_,_,_] x y z = 
    x :: y :: z :: []
pattern [_,_,_,_] w x y z = 
    w :: x :: y :: z :: []
pattern [_,_,_,_,_] v w x y z = 
    v :: w :: x :: y :: z :: []
pattern [_,_,_,_,_,_] u v w x y z = 
    u :: v :: w :: x :: y :: z :: []
pattern [_,_,_,_,_,_,_] t u v w x y z = 
    t :: u :: v :: w :: x :: y :: z :: []
pattern [_,_,_,_,_,_,_,_] s t u v w x y z = 
    s :: t :: u :: v :: w :: x :: y :: z :: []
pattern [_,_,_,_,_,_,_,_,_] r s t u v w x y z = 
    r :: s :: t :: u :: v :: w :: x :: y :: z :: []
pattern [_,_,_,_,_,_,_,_,_,_] q r s t u v w x y z = 
    q :: r :: s :: t :: u :: v :: w :: x :: y :: z :: []
pattern [_,_,_,_,_,_,_,_,_,_,_] p q r s t u v w x y z = 
    p :: q :: r :: s :: t :: u :: v :: w :: x :: y :: z :: []
pattern [_,_,_,_,_,_,_,_,_,_,_,_] o p q r s t u v w x y z = 
    o :: p :: q :: r :: s :: t :: u :: v :: w :: x :: y :: z :: []
pattern [_,_,_,_,_,_,_,_,_,_,_,_,_] n o p q r s t u v w x y z = 
    n :: o :: p :: q :: r :: s :: t :: u :: v :: w :: x :: y :: z :: []
pattern [_,_,_,_,_,_,_,_,_,_,_,_,_,_] m n o p q r s t u v w x y z = 
    m :: n :: o :: p :: q :: r :: s :: t :: u :: v :: w :: x :: y :: z :: []
pattern [_,_,_,_,_,_,_,_,_,_,_,_,_,_,_] l m n o p q r s t u v w x y z = 
    l :: m :: n :: o :: p :: q :: r :: s :: t :: u :: v :: w :: x :: y :: z :: []
pattern [_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_] k l m n o p q r s t u v w x y z = 
    k :: l :: m :: n :: o :: p :: q :: r :: s :: t :: u :: v :: w :: x :: y :: z :: []