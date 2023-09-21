module Relation.Property where

open import Agda.Primitive using (Level)

private 
    variable
        ℓ : Level

record Trans {A : Set ℓ} (_R_ : A → A → Set ℓ) : Set ℓ where 
    field
        trans : {x y z : A} → x R y → y R z → x R z
    infixl 20 _➤_ 
    infixr 20 _➤⟨_⟩_
    _➤_ : {x y z : A} → x R y → y R z → x R z
    _➤_ = trans

    _➤⟨_⟩_ : (x : A) {y z : A} → x R y → y R z → x R z
    x ➤⟨ xRy ⟩ yRz = trans xRy yRz
open Trans ⦃...⦄ public 

record Symm {A : Set ℓ} (_R_ : A → A → Set ℓ) : Set ℓ where 
    field
        symm : {x y : A} → x R y → y R x
open Symm ⦃...⦄ public

record Refl {A : Set ℓ} (_R_ : A → A → Set ℓ) : Set ℓ where 
    field 
        refl : {x : A} → x R x 
    infix 30 _□
    _□ : (x : A) → x R x
    _□ x = refl
open Refl ⦃...⦄ public 