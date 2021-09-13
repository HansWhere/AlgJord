module Relation.Equality where

open import Agda.Primitive using (Level)

private 
    variable
        ℓ ℓ' ℓ'' : Level

infixr 20 _≡⟨_⟩_ _≡⟨'_⟩_ _≡⟨⟩_
infix 30 _∎ _◈_ 
infixl 30 _➤_
infix 40 _≡_

data _≡_ {A : Set ℓ} (x : A) : A → Set ℓ where
    refl : x ≡ x
{-# BUILTIN EQUALITY _≡_ #-}

symm : {A : Set ℓ} {x y : A} → x ≡ y → y ≡ x
symm refl = refl

trans : {A : Set ℓ} {x y z : A} → x ≡ y → y ≡ z → x ≡ z
trans refl refl = refl
_➤_ = trans

cong : {A : Set ℓ} {B : Set ℓ'} {x y : A} (f : A → B) → x ≡ y → f x ≡ f y
cong f refl = refl

cong2 : {A : Set ℓ} {B : Set ℓ''} {C : Set ℓ''} {a₁ a₂ : A} {b₁ b₂ : B} (f : A → B → C) 
    → a₁ ≡ a₂ → b₁ ≡ b₂ 
    → f a₁ b₁ ≡ f a₂ b₂
cong2 f refl refl = refl

_◈_ : {A : Set ℓ} {B : Set ℓ'} {x y : A} (f : A → B) → x ≡ y → f x ≡ f y
f ◈ refl = refl

_≡⟨_⟩_ : {A : Set ℓ} (x : A) {y z : A} → x ≡ y → y ≡ z → x ≡ z
x ≡⟨ x≡y ⟩ y≡z = trans x≡y y≡z

_≡⟨'_⟩_ : {A : Set ℓ} (x : A) {y z : A} → y ≡ x → y ≡ z → x ≡ z
x ≡⟨' y≡x ⟩ y≡z = trans (symm y≡x) y≡z

_≡⟨⟩_ : {A : Set ℓ} (x : A) {y : A} → x ≡ y → x ≡ y
_≡⟨⟩_ = _≡⟨ refl ⟩_

_∎ : {A : Set ℓ} (x : A) → x ≡ x
_∎ x = refl

