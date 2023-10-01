module Relation.Order where
open import Agda.Primitive using (Level; lsuc; _⊔_)
open import Relation.Equivalance public
open import Logic.Connective using (_∧_; _⹁_; _∨_; lft; rgt)
open import Logic.Absurdum

private 
    variable
        ℓ ℓ' : Level
        A : Set ℓ

record PreOrd {A : Set ℓ} {_≃_ : A → A → Set ℓ} ⦃ _ : Eqv _≃_ ⦄ (_≤_ : A → A → Set ℓ) : Set ℓ where 
    field
        overlap ⦃ -Trans ⦄ : Trans _≤_
        overlap ⦃ -Refl ⦄ : Refl _≤_
    infixr 20 _≤⟨_⟩_ _≤⟨⟩_
    _≤⟨_⟩_ : (x : A) {y z : A} → x ≤ y → y ≤ z → x ≤ z
    x ≤⟨ x≤y ⟩ y≤z = trans x≤y y≤z

    _≤⟨⟩_ : (x : A) {y : A} → x ≤ y → x ≤ y
    _≤⟨⟩_ = _≤⟨ refl ⟩_

    data _<_ (x y : A) : Set ℓ where
        strict : x ≤ y → ¬ (x ≃ y) → x < y

open PreOrd ⦃...⦄ public hiding (-Trans; -Refl)

record Antisymm {A : Set ℓ} {_≃_ : A → A → Set ℓ} ⦃ _ : Eqv _≃_ ⦄ (_≤_ : A → A → Set ℓ) : Set ℓ where 
    field 
        antisymm : {x y : A} → x ≤ y → y ≤ x → x ≃ y
open Antisymm ⦃...⦄ public

record PartialOrd {A : Set ℓ} {_≃_ : A → A → Set ℓ} ⦃ _ : Eqv _≃_ ⦄ (_≤_ : A → A → Set ℓ) : Set ℓ where
    field
        overlap ⦃ -PreOrd ⦄ : PreOrd _≤_
        overlap ⦃ -Antisymm ⦄ : Antisymm _≤_
open PartialOrd ⦃...⦄ public
    
record Total {A : Set ℓ} {_≃_ : A → A → Set ℓ} ⦃ _ : Eqv _≃_ ⦄ (_≤_ : A → A → Set ℓ) : Set ℓ where 
    field
        total : (x y : A) → x ≤ y ∨ y ≤ x 
open Total ⦃...⦄ public 

record TotalOrd {A : Set ℓ} {_≃_ : A → A → Set ℓ} ⦃ _ : Eqv _≃_ ⦄ (_≤_ : A → A → Set ℓ) : Set ℓ where
    field
        overlap ⦃ -PartialOrd ⦄ : PartialOrd _≤_
        overlap ⦃ -Total ⦄ : Total _≤_
open TotalOrd ⦃...⦄ public




