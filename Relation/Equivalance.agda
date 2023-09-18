{-# OPTIONS --copatterns #-}
module Relation.Equivalance where
open import Agda.Primitive using (Level; lsuc; _⊔_)
open import Relation.Property using (Trans; trans; _➤_; Symm; symm; Refl; refl) public

private 
    variable
        ℓ ℓ' : Level

infixr 20 _≃⟨_⟩_ _≃⟨'_⟩_ _≃⟨⟩_
infix 30 _□

record Eqv {A : Set ℓ} (_≃_ : A → A → Set ℓ) : Set ℓ where 
    field
        overlap ⦃ -Trans ⦄ : Trans _≃_
        overlap ⦃ -Symm ⦄ : Symm _≃_
        overlap ⦃ -Refl ⦄ : Refl _≃_
-- open Eqv ⦃...⦄ public hiding (-Trans; -Symm; -Refl)

-- record ClsFun {A : Set ℓ} {B : Set ℓ'} (_≃_ : A → A → Set ℓ) ⦃ _ : Eqv _≃_ ⦄ (_≅_ : B → B → Set ℓ') ⦃ _ : Eqv _≅_ ⦄ : Set (ℓ ⊔ ℓ') where
--     field 
--         cong : {x y : A} → x ≃ y → f x ≅ f y
-- open Cong ⦃...⦄ public

-- Cong' : {A : Set ℓ} (_≃_ : A → A → Set ℓ) ⦃ _ : Eqv _≃_ ⦄ (f : A → A) → Set ℓ
-- Cong' _≃_ f = Cong _≃_ _≃_ f

record EqvSet (A : Set ℓ) : Set (lsuc ℓ) where
    field
        _≃_ : A → A → Set ℓ
        overlap ⦃ -Eqv ⦄ : Eqv _≃_
open EqvSet ⦃...⦄ public hiding (-Eqv)

_≃⟨_⟩_ : {A : Set ℓ} {_≃_ : A → A → Set ℓ} ⦃ _ : Trans _≃_ ⦄ (x : A) {y z : A} → x ≃ y → y ≃ z → x ≃ z
x ≃⟨ x≃y ⟩ y≃z = trans x≃y y≃z

_≃⟨'_⟩_ : {A : Set ℓ} {_≃_ : A → A → Set ℓ} ⦃ _ : Trans _≃_ ⦄ ⦃ _ : Symm _≃_ ⦄ (x : A) {y z : A} → y ≃ x → y ≃ z → x ≃ z
x ≃⟨' y≃x ⟩ y≃z = trans (symm y≃x) y≃z

_≃⟨⟩_ : {A : Set ℓ} {_≃_ : A → A → Set ℓ} ⦃ _ : Trans _≃_ ⦄ ⦃ _ : Refl _≃_ ⦄ (x : A) {y : A} → x ≃ y → x ≃ y
_≃⟨⟩_ = _≃⟨ refl ⟩_

_□ : {A : Set ℓ} {_≃_ : A → A → Set ℓ} ⦃ _ : Refl _≃_ ⦄ (x : A) → x ≃ x
_□ x = refl

