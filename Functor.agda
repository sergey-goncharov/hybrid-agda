{-# OPTIONS --cubical --safe #-}

open import Level using (Level) renaming (suc to ℓ-suc)
open import Function using (id; _∘_)
open import Category.Functor
open import Data.Product using (Σ; ∃-syntax; _×_; _,_; proj₁; proj₂)

open import CubicalIdentity using (_≡_; refl; cong; sym; trans; subst; subst-app; transport; transport-refl; →-≡)
open CubicalIdentity.≡-Reasoning

open import Category
open import Co-Cartesian

--*
{-
  This module introduces the notion of functor. 
-
  In this module functors are between categories from the module Category. 
  However, a shortcut definition for endofunctors on the category of Sets is also included
  together with a conversion to RawFunctor from the module Category.Functor. 
-}
--*

module Functor where

private
  variable
    ℓ : Level
    Ob Ob₁ Ob₂ : Set (ℓ-suc ℓ)
    C D E : Category Ob
    CoC : Co-Cartesian C
    Fₓ Gₓ : Ob₁ → Ob₂

record Functor (C₁ : Category {ℓ} Ob₁) (C₂ : Category {ℓ} Ob₂) (Fₓ : Ob₁ → Ob₂) : Set (ℓ-suc ℓ) where
  open Category.Category C₁ renaming (Obj to Obj₁; _➔_ to _➔₁_; idm to idm₁; _⊚_ to _⊚₁_)
  open Category.Category C₂ renaming (Obj to Obj₂; _➔_ to _➔₂_; idm to idm₂; _⊚_ to _⊚₂_)
  F : Obj₁ → Obj₂
  F = Fₓ
  
  field 
    fmap : ∀ {A B : Obj₁} → (A ➔₁ B) → ((F A) ➔₂ (F B))
    idF  : ∀ {A : Obj₁} → fmap {A} {A} idm₁ ≡ idm₂
    ∘F   : ∀ {A B C : Obj₁} {f : A ➔₁ B} {g : B ➔₁ C}
           → fmap (g ⊚₁ f) ≡ (fmap g) ⊚₂ (fmap f)

-- Identity functor
Id : Functor C C id
Id = 
  record 
    { fmap = id
    ; idF  = refl
    ; ∘F   = refl
    }

-- Functor composition
_G∘F_ : Functor D E Gₓ → Functor C D Fₓ → Functor C E (Gₓ ∘ Fₓ)
_G∘F_ GFun FFun = 
  record 
    { fmap = λ {A} {B} → (mapG {F A} {F B}) ∘ (fmap {A} {B})
    ; idF = trans (cong mapG idF) idG
    ; ∘F = trans (cong mapG ∘F) ∘G 
    }
  where
    open Functor FFun
    open Functor GFun renaming (F to G; fmap to mapG; idF to idG; ∘F to ∘G)

record ForgetfulFunctor (C : SetCategory {ℓ}) : Set (ℓ-suc ℓ) where
  open Category.Category C
  
  field 
    fmap : ∀ {A B : Obj} → (A ➔ B) → (A → B)
    idF  : ∀ {A : Obj} → fmap {A} {A} idm ≡ id
    ∘F   : ∀ {A B C : Obj} {f : A ➔ B} {g : B ➔ C} → 
             fmap (g ⊚ f) ≡ (fmap g) ∘ (fmap f)

ForgetfulFunctor→Functor : ∀ (C : SetCategory {ℓ}) → ForgetfulFunctor C → Functor C (SetCat {ℓ}) id
ForgetfulFunctor→Functor C Fun =
  record {
     fmap = fmap 
   ; idF  = idF
   ; ∘F   = ∘F
  } 
    where open ForgetfulFunctor Fun
    
-- Endofunctor on the category of Sets
SetFun : ∀ (F : Set ℓ → Set ℓ) → Set (ℓ-suc ℓ)
SetFun F = Functor SetCat SetCat F

-- Conversion to Category.RawFunctor from the standard library
SetRawFun : SetFun Fₓ → RawFunctor Fₓ
SetRawFun SFun = record { _<$>_ = fmap }
  where open Functor SFun

IdSet : SetFun {ℓ} id
IdSet = Id

-- Functor that strictly preserves co-Cartesian structure
record CoC-Functor (CoC₁ : Co-Cartesian C) (CoC₂ : Co-Cartesian D) 
                   (Fun : Functor {ℓ} C D Fₓ) : Set (ℓ-suc ℓ) where
  open Co-Cartesian.Co-Cartesian CoC₁ renaming (Obj to Obj₁; _➔_ to _➔₁_; idm to idm₁; _⊚_ to _⊚₁_;
                                                _⊎_ to _⊎₁_; inl to inl₁; inr to inr₁; [_,_] to [_,_]₁)
  open Co-Cartesian.Co-Cartesian CoC₂ renaming (Obj to Obj₂; _➔_ to _➔₂_; idm to idm₂; _⊚_ to _⊚₂_;
                                                _⊎_ to _⊎₂_; inl to inl₂; inr to inr₂; [_,_] to [_,_]₂)
  open Functor Fun public

  field
    ⊎F : ∀ {A B : Obj₁} → F (A ⊎₁ B) ≡ ((F A) ⊎₂ (F B))

  -- Conversion functions
  ⊎F→ : ∀ {A B : Obj₁} (P : Obj₂ → Set ℓ) → P (F (A ⊎₁ B)) → P ((F A) ⊎₂ (F B))
  ⊎F→ {A} {B} P = subst P ⊎F  

  ⊎F← : ∀ {A B : Obj₁} (P : Obj₂ → Set ℓ) → P ((F A) ⊎₂ (F B)) → P (F (A ⊎₁ B)) 
  ⊎F← {A} {B} P = subst P (sym ⊎F)

  field
    inlF : ∀ {A B : Obj₁} → inl₂ {F A} {F B} ≡ ⊎F→ (F A ➔₂_) (fmap (inl₁ {A} {B}))
    inrF : ∀ {A B : Obj₁} → inr₂ {F A} {F B} ≡ ⊎F→ (F B ➔₂_) (fmap (inr₁ {A} {B}))
    []F : ∀ {A B C : Obj₁} {f : A ➔₁ C} {g : B ➔₁ C} → 
            [ fmap f , fmap g ]₂ ≡ ⊎F→ (_➔₂ F C) (fmap [ f , g ]₁)
 
  ⊎F→⊚ : ∀ {A B : Obj₁} {C D : Obj₂} → (f : C ➔₂ F (A ⊎₁ B)) → (g : D ➔₂ C)
      → ⊎F→ (D ➔₂_) (f ⊚₂ g) ≡ (⊎F→ (C ➔₂_) f) ⊚₂ g  
  ⊎F→⊚{C = C}{D = D} f g = subst-app (C ➔₂_) {B₂ = D ➔₂_} (λ _ → _⊚₂ g) ⊎F

-- The identity functor strictly preserves co-Cartesian structure
IdmoCF : CoC-Functor CoC CoC Id
IdmoCF {CoC = CoC} =
  record
    { ⊎F = refl
    ; inlF = sym (transport-refl inl)
    ; inrF = sym (transport-refl inr)
    ; []F = λ {A} {B} {C} {f} {g} → sym (transport-refl [ f , g ])
    }
  where
    open Co-Cartesian.Co-Cartesian CoC

-- Free object
record FreeObject {C : SetCategory {ℓ}} (GFun : ForgetfulFunctor {ℓ} C) (A : Set ℓ) : Set (ℓ-suc ℓ) where

  open Category.Category C 
  open ForgetfulFunctor GFun using (fmap)

  field        
     F : Set ℓ
     η : A → F 
     _* : ∀ {Y : Set ℓ} → (A → Y) → F ➔ Y
     *-lift : ∀ {Y : Set ℓ} (f : A → Y) → fmap (f *) ∘ η ≡ f
     *-uniq : ∀ {Y : Set ℓ} (f : A → Y) (g : F ➔ Y) → (fmap g) ∘ η ≡ f → g ≡ f *

