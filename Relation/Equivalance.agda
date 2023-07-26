{-# OPTIONS --copatterns #-}
module Relation.Equivalance where
open import Agda.Primitive using (Level; lsuc)
open import Relation.Property using (Trans; trans; Symm; symm; Refl; refl) public

private 
    variable
        ℓ ℓ' : Level

infixr 20 _≃⟨_⟩_ _≃⟨'_⟩_ _≃⟨⟩_
infix 30 _●

record Eqv {A : Set ℓ} (_≃_ : A → A → Set ℓ) : Set ℓ where 
    field
        overlap ⦃ -Trans ⦄ : Trans _≃_
        overlap ⦃ -Symm ⦄ : Symm _≃_
        overlap ⦃ -Refl ⦄ : Refl _≃_
open Eqv ⦃...⦄ public hiding (-Trans; -Symm; -Refl)

record EqvSet (A : Set ℓ) : Set (lsuc ℓ) where
    field
        _≃_ : A → A → Set ℓ
        -Eqv : Eqv _≃_
open EqvSet ⦃...⦄ public

_≃⟨_⟩_ : {A : Set ℓ} {_≃_ : A → A → Set ℓ} ⦃ _ : Trans _≃_ ⦄ (x : A) {y z : A} → x ≃ y → y ≃ z → x ≃ z
x ≃⟨ x≃y ⟩ y≃z = trans x≃y y≃z

_≃⟨'_⟩_ : {A : Set ℓ} {_≃_ : A → A → Set ℓ} ⦃ _ : Trans _≃_ ⦄ ⦃ _ : Symm _≃_ ⦄ (x : A) {y z : A} → y ≃ x → y ≃ z → x ≃ z
x ≃⟨' y≃x ⟩ y≃z = trans (symm y≃x) y≃z

_≃⟨⟩_ : {A : Set ℓ} {_≃_ : A → A → Set ℓ} ⦃ _ : Trans _≃_ ⦄ ⦃ _ : Refl _≃_ ⦄ (x : A) {y : A} → x ≃ y → x ≃ y
_≃⟨⟩_ = _≃⟨ refl ⟩_

_● : {A : Set ℓ} {_≃_ : A → A → Set ℓ} ⦃ _ : Refl _≃_ ⦄ (x : A) → x ≃ x
_● x = refl