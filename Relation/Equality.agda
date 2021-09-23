module Relation.Equality where

open import Agda.Primitive using (Level)

private 
    variable
        ℓ ℓ' : Level 
        ℓ₁ ℓ₂ ℓ₃ ℓ₄ : Level

infixr 20 _≡⟨_⟩_ _≡⟨'_⟩_ _≡⟨⟩_
infix 30 _∎ _◈_ 
infixl 20 _➤_ _➤'_ _➤`_
infix 40 _≡_

data _≡_ {A : Set ℓ} (x : A) : A → Set ℓ where
    refl : x ≡ x
{-# BUILTIN EQUALITY _≡_ #-}

symm : {A : Set ℓ} {x y : A} → x ≡ y → y ≡ x
symm refl = refl

trans : {A : Set ℓ} {x y z : A} → x ≡ y → y ≡ z → x ≡ z
trans refl refl = refl

_➤_ : {A : Set ℓ} {x y z : A} → x ≡ y → y ≡ z → x ≡ z
_➤_ = trans

_➤'_ : {A : Set ℓ} {x y z : A} → y ≡ x → y ≡ z → x ≡ z
y≡x ➤' y≡z = trans (symm y≡x) y≡z

_➤`_ : {A : Set ℓ} {x y z : A} → x ≡ y → z ≡ y → x ≡ z
x≡y ➤` z≡y = trans x≡y (symm z≡y)

cong : {A : Set ℓ} {B : Set ℓ'} {x y : A} (f : A → B) → x ≡ y → f x ≡ f y
cong f refl = refl

cong2 : {A : Set ℓ₁} {B : Set ℓ₂} {C : Set ℓ'} {a₁ a₂ : A} {b₁ b₂ : B} (f : A → B → C) 
    → a₁ ≡ a₂ → b₁ ≡ b₂ 
    → f a₁ b₁ ≡ f a₂ b₂
cong2 f refl refl = refl

cong3 : {A : Set ℓ₁} {B : Set ℓ₂} {C : Set ℓ₃} {D : Set ℓ'} 
    {a₁ a₂ : A} {b₁ b₂ : B} {c₁ c₂ : C} (f : A → B → C → D) 
    → a₁ ≡ a₂ → b₁ ≡ b₂ → c₁ ≡ c₂
    → f a₁ b₁ c₁ ≡ f a₂ b₂ c₂
cong3 f refl refl refl = refl

cong4 : {A : Set ℓ₁} {B : Set ℓ₂} {C : Set ℓ₃} {D : Set ℓ₄} {E : Set ℓ} 
    {a₁ a₂ : A} {b₁ b₂ : B} {c₁ c₂ : C} {d₁ d₂ : D} (f : A → B → C → D → E) 
    → a₁ ≡ a₂ → b₁ ≡ b₂ → c₁ ≡ c₂ → d₁ ≡ d₂
    → f a₁ b₁ c₁ d₁ ≡ f a₂ b₂ c₂ d₂
cong4 f refl refl refl refl = refl

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

