module Relation.Equality where

open import Agda.Primitive using (Level)
open import Logic.Absurdum

import Relation.Equivalance as ≃

private 
    variable
        ℓ ℓ' : Level 
        ℓA ℓB ℓC ℓD ℓE ℓF ℓG ℓH ℓI : Level
        A : Set ℓA
        B : Set ℓB
        C : Set ℓC
        D : Set ℓD
        E : Set ℓE
        F : Set ℓF
        G : Set ℓG
        H : Set ℓH
        I : Set ℓI
        x y z a₁ a₂ : A
        b₁ b₂ : B
        c₁ c₂ : C
        d₁ d₂ : D
        e₁ e₂ : E
        f₁ f₂ : F
        g₁ g₂ : G
        h₁ h₂ : H

infixr 20 _≡⟨_⟩_ _≡⟨'_⟩_ _≡⟨⟩_
infix 30 _∎ _◈_ 
infixl 20 _≡➤_ _≡➤'_ _≡➤`_
infix 40 _≡_

data _≡_ {A : Set ℓA} (x : A) : A → Set ℓA where
    refl : x ≡ x
{-# BUILTIN EQUALITY _≡_ #-}

_≠_ : {A : Set ℓA} → A → A → Set ℓA
x ≠ y = ¬ x ≡ y

symm : {x y : A} → x ≡ y → y ≡ x
symm refl = refl

trans : {x y z : A} → x ≡ y → y ≡ z → x ≡ z
trans refl refl = refl

_≡➤_ : {x y z : A} → x ≡ y → y ≡ z → x ≡ z
_≡➤_ = trans

_≡➤'_ : {x y z : A} → y ≡ x → y ≡ z → x ≡ z
y≡x ≡➤' y≡z = trans (symm y≡x) y≡z

_≡➤`_ : {x y z : A} → x ≡ y → z ≡ y → x ≡ z
x≡y ≡➤` z≡y = trans x≡y (symm z≡y)

cong : {x y : A} (f : A → B) → x ≡ y → f x ≡ f y
cong f refl = refl

cong2 : (f : A → B → C) 
    → a₁ ≡ a₂ → b₁ ≡ b₂ 
    → f a₁ b₁ ≡ f a₂ b₂
cong2 f refl refl = refl

cong3 : (f : A → B → C → D) 
    → a₁ ≡ a₂ → b₁ ≡ b₂ → c₁ ≡ c₂
    → f a₁ b₁ c₁ ≡ f a₂ b₂ c₂
cong3 f refl refl refl = refl

cong4 : (f : A → B → C → D → E) 
    → a₁ ≡ a₂ → b₁ ≡ b₂ → c₁ ≡ c₂ → d₁ ≡ d₂
    → f a₁ b₁ c₁ d₁ ≡ f a₂ b₂ c₂ d₂
cong4 f refl refl refl refl = refl

cong5 : (f : A → B → C → D → E → F) 
    → a₁ ≡ a₂ → b₁ ≡ b₂ → c₁ ≡ c₂ → d₁ ≡ d₂ → e₁ ≡ e₂
    → f a₁ b₁ c₁ d₁ e₁ ≡ f a₂ b₂ c₂ d₂ e₂
cong5 f refl refl refl refl refl = refl

cong6 : (f : A → B → C → D → E → F → G) 
    → a₁ ≡ a₂ → b₁ ≡ b₂ → c₁ ≡ c₂ → d₁ ≡ d₂ → e₁ ≡ e₂ → f₁ ≡ f₂
    → f a₁ b₁ c₁ d₁ e₁ f₁ ≡ f a₂ b₂ c₂ d₂ e₂ f₂
cong6 f refl refl refl refl refl refl = refl

cong7 : (f : A → B → C → D → E → F → G → H) 
    → a₁ ≡ a₂ → b₁ ≡ b₂ → c₁ ≡ c₂ → d₁ ≡ d₂ → e₁ ≡ e₂ → f₁ ≡ f₂ → g₁ ≡ g₂
    → f a₁ b₁ c₁ d₁ e₁ f₁ g₁ ≡ f a₂ b₂ c₂ d₂ e₂ f₂ g₂
cong7 f refl refl refl refl refl refl refl = refl

cong8 : (f : A → B → C → D → E → F → G → H → I) 
    → a₁ ≡ a₂ → b₁ ≡ b₂ → c₁ ≡ c₂ → d₁ ≡ d₂ → e₁ ≡ e₂ → f₁ ≡ f₂ → g₁ ≡ g₂ → h₁ ≡ h₂
    → f a₁ b₁ c₁ d₁ e₁ f₁ g₁ h₁ ≡ f a₂ b₂ c₂ d₂ e₂ f₂ g₂ h₂
cong8 f refl refl refl refl refl refl refl refl = refl

_◈_ : (f : A → B) → x ≡ y → f x ≡ f y
f ◈ refl = refl

_≡⟨_⟩_ : (x : A) → x ≡ y → y ≡ z → x ≡ z
x ≡⟨ x≡y ⟩ y≡z = trans x≡y y≡z

_≡⟨'_⟩_ : (x : A) → y ≡ x → y ≡ z → x ≡ z
x ≡⟨' y≡x ⟩ y≡z = trans (symm y≡x) y≡z

_≡⟨⟩_ : (x : A) → x ≡ y → x ≡ y
_≡⟨⟩_ = _≡⟨ refl ⟩_

_∎ : (x : A) → x ≡ x
_∎ x = refl

instance
    ≡-Refl : {A : Set ℓ'} → ≃.Refl {ℓ'} {A} _≡_
    ≃.Refl.refl ≡-Refl = refl

    ≡-Symm : {A : Set ℓ'} → ≃.Symm {ℓ'} {A} _≡_
    ≃.Symm.symm ≡-Symm = symm

    ≡-Trans : {A : Set ℓ'} → ≃.Trans {ℓ'} {A} _≡_
    ≃.Trans.trans ≡-Trans = trans

    ≡-Eqv : {A : Set ℓ'} → ≃.Eqv {ℓ'} {A} _≡_
    ≃.Eqv.-Refl ≡-Eqv = ≡-Refl 
