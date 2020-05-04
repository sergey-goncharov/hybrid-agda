{-# OPTIONS --cubical --safe #-}

open import Level using (Level) renaming (suc to ℓ-suc)
open import Function using (id; _∘_; _$_; flip)
import Data.Sum as Sum using (_⊎_; inj₁; inj₂; [_,_])
open import Category.Monad

open import CubicalIdentity using (_≡_; refl; sym; trans; cong; subst; transport; transport-refl)
open CubicalIdentity.≡-Reasoning

open import Category
open import Co-Cartesian
open import Functor

--*
{-
  This module introduces the notion of Kleisli triple and Kleisli category. 
-
  A conversion to Haskell style monads without the monad laws is also included. 
-}
--*

module Kleisli where

private
  variable
    ℓ ℓ′ : Level
    Gₓ : Set ℓ → Set ℓ′

record Kleisli (T : Set ℓ → Set ℓ) : Set (ℓ-suc ℓ) where
  infixr  1 _⟶_
  infix  10 _⋄_

  -- Kleisli maps
  _⟶_ : Set ℓ → Set ℓ → Set ℓ
  _⟶_ X Y = X → T Y 
  
  field
    ηₓ : ∀ {X : Set ℓ} → (X ⟶ X)
    _* : ∀ {X Y : Set ℓ} → (X ⟶ Y) → (T X ⟶ Y)
  
  -- Set ℓ and _⟶_ with idₖ and _⋄_ form the Kleisli category
  idₖ : ∀ {A : Set ℓ} → (A ⟶ A)
  idₖ = ηₓ
  _⋄_ : ∀ {A B C : Set ℓ} → (B ⟶ C) → (A ⟶ B) → (A ⟶ C)
  _⋄_ g f = g * ∘ f

  -- ⋄-assoc : ∀ {A B C D : Set ℓ} {f : A ⟶ B} {g : B ⟶ C} {h : C ⟶ D}
  --     → h ⋄ (g ⋄ f) ≡ (h ⋄ g) ⋄ f
  -- ⋄-assoc = {!!}    
  
  field
    ηₓ-unitˡ : ∀ {X : Set ℓ} → (ηₓ {X}) * ≡ id {A = T X}
    ηₓ-unitʳ : ∀ {X Y : Set ℓ} {f : X ⟶ Y} → f ⋄ ηₓ ≡ f
    *-assoc : ∀ {X Y Z : Set ℓ} {f : X ⟶ Y} {g : Y ⟶ Z} → (g ⋄ f) * ≡ g ⋄ f *

  -- Kleisli category
  Kl : SetCategory
  Kl = record 
         { _➔_ = _⟶_
         ; idm = idₖ
         ; _⊚_ = _⋄_
         ; ⊚-unitˡ = λ {A} {B} {f} → cong (_∘ f) ηₓ-unitˡ
         ; ⊚-unitʳ = ηₓ-unitʳ
         ; ⊚-assoc = λ {A} {B} {C} {D} {f} {g} {h} → sym (cong (_∘ f) *-assoc)
         }
  Kl-CoC : Co-Cartesian Kl
  Kl-CoC = record
         { _⊎_ = Sum._⊎_
         ; inl = ηₓ ∘ Sum.inj₁
         ; inr = ηₓ ∘ Sum.inj₂
         ; [_,_] = Sum.[_,_]
         ; []-inl = λ {A} {B} {C} {f} {g} → 
             begin
               Sum.[ f , g ] ⋄ ηₓ ∘ Sum.inj₁
             ≡⟨ cong (λ h → h ∘ Sum.inj₁) ηₓ-unitʳ ⟩
               f
             ∎
         ; []-inr = λ {A} {B} {C} {f} {g} → 
             begin
               Sum.[ f , g ] ⋄ ηₓ ∘ Sum.inj₂
             ≡⟨ cong (λ h → h ∘ Sum.inj₂) ηₓ-unitʳ ⟩
               g
             ∎
         ; [inl,inr] = λ {A} {B} → 
             begin
               Sum.[ ηₓ ∘ Sum.inj₁ , ηₓ ∘ Sum.inj₂ ]
             ≡⟨ sym (Co-Cartesian.⊚-distrib-[] SetCoC {f = Sum.inj₁} {g = Sum.inj₂} {h = ηₓ}) ⟩
               ηₓ ∘ Sum.[ Sum.inj₁ , Sum.inj₂ ]
             ≡⟨ cong (λ h → ηₓ ∘ h) (Co-Cartesian.[inl,inr] SetCoC) ⟩
               ηₓ
             ∎
         ; ⊚-distrib-[] = λ {A} {B} {C} {D} {f} {g} {h} → 
             begin
               h ⋄ Sum.[ f , g ]
             ≡⟨ Co-Cartesian.⊚-distrib-[] SetCoC {f = f} {g = g} {h = h *} ⟩
               Sum.[ h ⋄ f , h ⋄ g ]
             ∎
         }

  C→Kl : Functor SetCat Kl id
  C→Kl =
    record
      { fmap = λ f → ηₓ ∘ f
      ; idF = refl
      ; ∘F = λ {A} {B} {C} {f} {g} →
             begin
               ηₓ ∘ (g ∘ f)
             ≡⟨ refl ⟩
               (ηₓ ∘ g) ∘ f
             ≡⟨ cong (_∘ f) (sym ηₓ-unitʳ) ⟩
               ((ηₓ ∘ g) ⋄ ηₓ) ∘ f
             ≡⟨ refl ⟩
               (ηₓ ∘ g) ⋄ (ηₓ ∘ f)
             ∎
      }
  CoC-C→Kl : CoC-Functor SetCoC Kl-CoC C→Kl
  CoC-C→Kl =
    record
      { ⊎F = refl
      ; inlF = sym (transport-refl (ηₓ ∘ Sum.inj₁))
      ; inrF = sym (transport-refl (ηₓ ∘ Sum.inj₂))
      ; []F = λ {A} {B} {C} {f} {g} → sym (begin
                                             transport (λ i → id (A Sum.⊎ B) ⟶ C) (ηₓ ∘ (Sum.[ f , g ]))
                                           ≡⟨ transport-refl (ηₓ ∘ Sum.[ f , g ]) ⟩
                                             ηₓ ∘ Sum.[ f , g ]
                                           ≡⟨ (Co-Cartesian.⊚-distrib-[] SetCoC {h = ηₓ}) ⟩
                                             Sum.[ ηₓ ∘ f , ηₓ ∘ g ]
                                           ∎)
      }

  -- Haskell style Monad (without monad laws)
  RM : RawMonad T
  RM = record { return = ηₓ; _>>=_ = flip _* }
  
  -- Monad functor on T induced by the Kleisli triple
  Fun : SetFun T
  Fun = record 
          { fmap = λ f → (ηₓ ∘ f) *
          ; idF = ηₓ-unitˡ
          ; ∘F = λ {A} {B} {C} {f} {g} → 
                 begin
                   (ηₓ ∘ g ∘ f) *
                 ≡⟨ sym (cong (λ h → (h ∘ f) *) ηₓ-unitʳ) ⟩
                   ((ηₓ ∘ g) ⋄ ηₓ ∘ f) *
                 ≡⟨ *-assoc ⟩
                   (ηₓ ∘ g) ⋄ (ηₓ ∘ f) *
                 ∎
          }

idK : Kleisli {ℓ} id
idK = 
  record 
    { ηₓ = id
    ; _* = id
    ; ηₓ-unitˡ = refl
    ; ηₓ-unitʳ = refl
    ; *-assoc = refl
    }

-- existence of all free objects yields a monad
FreeObj→Kleisli : ∀ (D : SetCategory {ℓ}) (GFun : ForgetfulFunctor D) (FFun : ∀ X → FreeObject GFun X)
  → Kleisli (FreeObject.F ∘ FFun)
FreeObj→Kleisli D GFun FFun =
  record
   {
       ηₓ = λ {X} x → FFun X . FreeObject.η x
     ; _* = λ {X}{Y} f → fmap (FFun X . FreeObject._* f) 
     ; ηₓ-unitˡ = λ {X} →
          let open FreeObject (FFun X); open Category.Category D in
            trans (cong fmap (sym $ *-uniq η idm $ cong (_∘ η) idF)) idF
     ; ηₓ-unitʳ = λ {X}{Y}{f} →
          let open FreeObject (FFun X); open Category.Category D in
            *-lift f
     ; *-assoc = λ {X Y Z} {f}{g} →
          let
              open FreeObject (FFun X) renaming (η to ηˣ; _* to _*ˣ; *-uniq to *-uniqˣ)
              open FreeObject (FFun Y) using () renaming (η to ηʸ; _* to _*ʸ; *-uniq to *-uniqʸ)
              open Category.Category D
          in
            trans (cong fmap $ sym $ *-uniqˣ (fmap (g *ʸ) ∘ f) (g *ʸ ⊚ f *ˣ) $
              trans (cong (_∘ ηˣ) ∘F) (cong (fmap (g *ʸ) ∘_) $ *-lift f)) ∘F
   }
     where open Functor.ForgetfulFunctor GFun

