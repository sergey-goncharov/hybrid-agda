{-# OPTIONS --cubical --safe #-}

open import Level using (Level) renaming (suc to ℓ-suc)
open import Function using (id; _∘_)


open import CubicalIdentity using (_≡_; refl; sym; trans; cong)

--*
{-
  This module introduces the notion of category.
-
  Furthermore, it shows that Set ℓ with functions f : A → B as morphisms,
  and id and _∘_ as identity and composition, respectively, forms a category.
  However, since all the proofs are just refl, these results are used
  implicitly throughout the project.
-}
--*

module Category where

private
  variable
    ℓ : Level

record Category (Ob : Set (ℓ-suc ℓ)) : Set (ℓ-suc ℓ) where
  infixr 1 _➔_
  infix  9 _⊚_

  -- Objects
  Obj : Set (ℓ-suc ℓ)
  Obj = Ob
  field
    -- Morphisms
    _➔_ : ∀ (A B : Obj) → Set ℓ
    
    -- Identity
    idm : ∀ {A : Obj} → (A ➔ A) 

    -- Composition
    _⊚_ : ∀ {A B C : Obj} → (B ➔ C) → (A ➔ B) → (A ➔ C)

    -- Category laws
    ⊚-unitˡ : ∀ {A B : Obj} {f : A ➔ B} → idm ⊚ f ≡ f
    ⊚-unitʳ : ∀ {A B : Obj} {f : A ➔ B} → f ⊚ idm ≡ f
    ⊚-assoc : ∀ {A B C D : Obj} {f : A ➔ B} {g : B ➔ C} {h : C ➔ D}
      → h ⊚ (g ⊚ f) ≡ (h ⊚ g) ⊚ f

  ⊚-cong : ∀ {A B C : Obj} {f : B ➔ C} {f′ : B ➔ C} {g : A ➔ B} {g′ : A ➔ B} 
     → f ≡ f′ → g ≡ g′ → f ⊚ g ≡ f′ ⊚ g′
  ⊚-cong {f = f} {f′ = f′} {g = g} {g′ = g′} f≡f′ g≡g′ = trans (cong (_⊚_ f) g≡g′) (cong (_⊚ g′) f≡f′) 

  ⊚-cong₁ : ∀ {A B C : Obj} {f : B ➔ C} {f′ : B ➔ C} {g : A ➔ B}  
     → f ≡ f′ → f ⊚ g ≡ f′ ⊚ g
  ⊚-cong₁ {C = C} f≡f′ = ⊚-cong f≡f′ refl
  
  ⊚-cong₂ :  ∀ {A B C : Obj} {f : B ➔ C} {g : A ➔ B} {g′ : A ➔ B} 
     → g ≡ g′ → f ⊚ g ≡ f ⊚ g′
  ⊚-cong₂ {C = C} g≡g′ = ⊚-cong refl g≡g′


-- A category with elements of Set ℓ as objects
SetCategory : Set (ℓ-suc ℓ)
SetCategory {ℓ} = Category (Set ℓ)

SetCat : SetCategory {ℓ}
SetCat =
  record
    { _➔_ = λ A B → A → B
    ; idm = id
    ; _⊚_ = λ g f → g ∘ f
    ; ⊚-unitˡ = refl
    ; ⊚-unitʳ = refl
    ; ⊚-assoc = refl
    }

