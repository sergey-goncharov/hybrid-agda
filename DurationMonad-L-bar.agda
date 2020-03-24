{-# OPTIONS --cubical --safe #-}

open import Level using (Level; _⊔_) renaming (suc to ℓ-suc)
open import Function using (id; _∘_; _$_)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (_⊎_; inj₁; inj₂; [_,_])
open import Data.Product using (_,_; proj₁; proj₂)
open import Data.Nat using (ℕ; zero; suc)
                     renaming (_⊔_ to _⊔ᴺ_; _+_ to _+ᴺ_; _≤_ to _≤ᴺ_; z≤n to z≤ᴺn; s≤s to s≤ᴺs; ≤-pred to ≤ᴺ-pred)
open import Data.Nat.Properties using (m≤m⊔n; n≤m⊔n; +-suc; +-identityʳ; _≤?_)

open import CubicalIdentity using (_≡_; refl; sym; cong; cong2; trans; →-≡)
open CubicalIdentity.≡-Reasoning

open import Category
open import Co-Cartesian
open import Monoid
open import MonoidModule
open import Kleisli
open import ElgotIteration
open import PartialOrder hiding (_[_])
open import CompletePartialOrder

import Eliminators-L-bar

--*
{-
  This module defines the duration monad L̅ by initiality of L̅.
-}
--*

module DurationMonad-L-bar {ℓ ℓ′ : Level} {M : Monoid} (OM : O-Monoid {ℓ} {ℓ′} M) where

open Eliminators-L-bar OM
open Def-L̅

open DirSeq

L̅-DurationMonad : Kleisli L̅
L̅-DurationMonad =
  record
    { ηₓ = η
    ; _* = λ {X} {Y} f → fun (H (L̅-Initial X) (L̅*-COMMo f))
    ; ηₓ-unitˡ = λ {X} → uniq (L̅-Initial X) {CCOMMo′ = L̅-COMMo X} COMMMo-id
    ; ηₓ-unitʳ = λ {X} {Y} {f} → f-η (H (L̅-Initial X) (L̅*-COMMo f))
    ; *-assoc = λ {X} {Y} {Z} {f} {g} → uniq (L̅-Initial X) {CCOMMo′ = L̅*-COMMo ((fun (G f g)) ∘ f)} ((G′ f g) COMMMo-∘ H (L̅-Initial X) (L̅*-COMMo f))
    }
  where
    open Complete-OM-Module-Morphism-over using (COMMM; fun; f-η)
    open Initial-C-Complete-OM-Module-over using (H; uniq)
    module _ {X Y Z : Set (ℓ ⊔ ℓ′)} (f : X → L̅ Y) (g : Y → L̅ Z) where
      G : C-Complete-OM-Module-Morphism-over (L̅-COMMo Y) (L̅*-COMMo g)
      G = H (L̅-Initial Y) (L̅*-COMMo g)
      G′ : C-Complete-OM-Module-Morphism-over (L̅*-COMMo f) (L̅*-COMMo ((fun G) ∘ f))
      G′ = record
             { COMMM = COMMM G
             ; f-η = refl
             }

open Kleisli.Kleisli L̅-DurationMonad

module _ {X Y Z : Set (ℓ ⊔ ℓ′)} where

  open Complete-OM-Module-Morphism-over using (f-⊑; f-⨆; f-η)
  open Initial-C-Complete-OM-Module-over using (H; uniq)

  private
    _⊑ʸ_ = _⊑_ Y
    _⊑ᶻ_ = _⊑_ Z

    PO-⊑ˣʸ = →-PO (PO-⊑ Y) X
    DCPO-⊑ˣʸ = →-DCPO (Complete-OM-Module.DCPO-⊑ (L̅-COMM Y)) X
    ⨆ˣʸ = D-CompletePartialOrder.⨆ DCPO-⊑ˣʸ
    PO-⊑ˣᶻ = →-PO (PO-⊑ Z) X
    DCPO-⊑ˣᶻ = →-DCPO (Complete-OM-Module.DCPO-⊑ (L̅-COMM Z)) X
    ⨆ˣᶻ = D-CompletePartialOrder.⨆ DCPO-⊑ˣᶻ
    PO-⊑ʸᶻ = →-PO (PO-⊑ Z) Y
    DCPO-⊑ʸᶻ = →-DCPO (Complete-OM-Module.DCPO-⊑ (L̅-COMM Z)) Y
    ⨆ʸᶻ = D-CompletePartialOrder.⨆ DCPO-⊑ʸᶻ
    PO-⊑ʸ*ᶻ = →-PO (PO-⊑ Z) (L̅ Y)
    DCPO-⊑ʸ*ᶻ = →-DCPO (Complete-OM-Module.DCPO-⊑ (L̅-COMM Z)) (L̅ Y)
    ⨆ʸ*ᶻ = D-CompletePartialOrder.⨆ DCPO-⊑ʸ*ᶻ

  *-monoˡ′ : Mono PO-⊑ʸᶻ (→-PO (PO-⊑ Z) (L̅ Y)) (_*)
  *-monoˡ′ {g₁} {g₂} g₁x⊑g₂x = L̅-rec
    where
      args : Arguments Y
      args = record
               { P-L̅ = λ x → (g₁ *) x ⊑ᶻ (g₂ *) x
               ; P-⊑ = λ _ _ _ → ⊤
               ; P-▷ = λ a → ▷-monoʳ
               ; P-⊥ = ⊑-refl
               ; P-⨆ = λ { (p-seq , p-inc) → ⨆-lub (λ n → ⊑-trans (p-seq n) (⨆-ub n)) }
               ; P-η = g₁x⊑g₂x
               ; P-⊑-antisym = λ px py _ _ → ⊑-prop _ _
               ; P-⊑-prop = λ { _ _ tt tt → refl }
               }
      elims : Eliminators Y args
      elims = L̅-Elim Y args
      open Eliminators elims using (L̅-rec) public

  *-monoˡ : ∀ (f : X → L̅ Y) → Mono PO-⊑ʸᶻ PO-⊑ˣᶻ (_⋄ f)
  *-monoˡ f g₁x⊑g₂x x = *-monoˡ′ g₁x⊑g₂x (f x)

  *-monoʳ : ∀ (g : Y → L̅ Z) → Mono PO-⊑ˣʸ PO-⊑ˣᶻ (g ⋄_) 
  *-monoʳ g f₁x⊑f₂x x = f-⊑ (H (L̅-Initial Y) (L̅*-COMMo g)) (f₁x⊑f₂x x)

  *-contˡ′ : Cont DCPO-⊑ʸᶻ (→-DCPO (Complete-OM-Module.DCPO-⊑ (L̅-COMM Z)) (L̅ Y)) (_* ↑  *-monoˡ′)
  *-contˡ′ (seq ⇗ dir) = sym (uniq (L̅-Initial Y) {CCOMMo′ = L̅-CCOMMoYZ} h')
    where
      open D-CompletePartialOrder (Complete-OM-Module.DCPO-⊑ (L̅-COMM Z))
           renaming (⊑-antisym to ⊑ᶻ-antisym; ⊑-trans to ⊑ᶻ-trans; ⨆ to ⨆ᶻ;
             ⨆-ub to ⨆ᶻ-ub; ⨆-lub to ⨆ᶻ-lub; ⨆-const to ⨆ᶻ-const)

      h : C-Complete-OM-Module-Morphism (L̅-CCOMM Y) (L̅-CCOMM Z)   
      h = record
            { fun = λ x → ⨆ᶻ (DirSeq-mono { PO = PO-⊑ʸᶻ} (seq ⇗ dir) ((λ h → (h *) x) ↑ (λ h → *-monoˡ′ h x)))
            ; f-⊑ = λ x⊑y → ⨆ᶻ-lub (λ n → ⊑ᶻ-trans (f-⊑ (H (L̅-Initial Y) (L̅*-COMMo (seq n))) x⊑y) (⨆ᶻ-ub n))
            ; f-⊥ = ⨆ᶻ-const 
            ; f-▷ = Complete-OM-Module.▷-contʳ (L̅-COMM Z) 
            ; f-⨆ = ⊑ᶻ-antisym (⨆ᶻ-lub (λ n → ⨆ᶻ-lub (λ m → ⊑ᶻ-trans (⨆ᶻ-ub n) (⨆ᶻ-ub m))))
                              (⨆ᶻ-lub (λ n → ⨆ᶻ-lub (λ m → ⊑ᶻ-trans (⨆ᶻ-ub n) (⨆ᶻ-ub m))))
            }

      L̅-CCOMMoYZ : C-Complete-OM-Module-over Y OM (L̅-CCOMM Z)
      L̅-CCOMMoYZ = record { η = ⨆ʸᶻ (seq ⇗ dir) }

      h' : C-Complete-OM-Module-Morphism-over (L̅-COMMo Y) L̅-CCOMMoYZ 
      h' = record
             { COMMM = h
             ; f-η = →-≡ (λ x → ⊑ᶻ-antisym (⨆-lub (λ n → ⨆-ub n)) (⨆-lub (λ n → ⨆-ub n)))
             }
  
  *-contˡ : ∀ (f : X → L̅ Y) → Cont DCPO-⊑ʸᶻ DCPO-⊑ˣᶻ (_⋄ f ↑ *-monoˡ f)
  *-contˡ f s = →-≡ (λ x → (cong (λ k → k (f x)) (*-contˡ′ s)))

  *-contʳ : ∀ (g : Y → L̅ Z) → Cont DCPO-⊑ˣʸ DCPO-⊑ˣᶻ (g ⋄_ ↑ *-monoʳ g)
  *-contʳ g (seq ⇗ dir) = →-≡ (λ x → sym (f-⨆ (H (L̅-Initial Y) (L̅*-COMMo g))
                                                 {s =  (λ n → seq n x) ⇗ λ n m →
                                                            (proj₁ $ dir n m) , 
                                                            (proj₁ $ proj₂ $ dir n m) x ,
                                                            (proj₂ $ proj₂ $ dir n m) x
                                                  })) 

  *-⊥ : ∀ {f : X → L̅ Y} → (f *) ⊥ ≡ ⊥
  *-⊥ = refl

module _ {X Y Z : Set (ℓ ⊔ ℓ′)} where

  private 
    _⊑ʸ_ = _⊑_ Y
    DCPO-⊑ʸ = Complete-OM-Module.DCPO-⊑ (L̅-COMM Y)
    ωCPO-⊑ʸ = DCPO→ωCPO (PO-⊑ Y) DCPO-⊑ʸ 

    _⊑ᶻ_ = _⊑_ Z
    ωCPO-⊑ᶻ = DCPO→ωCPO (PO-⊑ Z) (Complete-OM-Module.DCPO-⊑ (L̅-COMM Z))
    
    PO-⊑ˣʸ = →-PO (PO-⊑ Y) X
    DCPO-⊑ˣʸ = →-DCPO (Complete-OM-Module.DCPO-⊑ (L̅-COMM Y)) X
    ωCPO-⊑ˣʸ = DCPO→ωCPO PO-⊑ˣʸ DCPO-⊑ˣʸ
    ⨆ˣʸ = ω-CompletePartialOrder.⨆ ωCPO-⊑ˣʸ
                                   
    PO-⊑ˣᶻ = →-PO (PO-⊑ Z) X
    DCPO-⊑ˣᶻ = →-DCPO (Complete-OM-Module.DCPO-⊑ (L̅-COMM Z)) X
    ωCPO-⊑ˣᶻ = DCPO→ωCPO PO-⊑ˣᶻ DCPO-⊑ˣᶻ
    _⊑ˣᶻ_ = ω-CompletePartialOrder._⊑_ ωCPO-⊑ˣᶻ
    ⨆ˣᶻ = ω-CompletePartialOrder.⨆ ωCPO-⊑ˣᶻ
    
    PO-⊑ʸᶻ = →-PO (PO-⊑ Z) Y
    DCPO-⊑ʸᶻ = →-DCPO (Complete-OM-Module.DCPO-⊑ (L̅-COMM Z)) Y
    ωCPO-⊑ʸᶻ = DCPO→ωCPO PO-⊑ʸᶻ DCPO-⊑ʸᶻ
    ⨆ʸᶻ = ω-CompletePartialOrder.⨆ ωCPO-⊑ʸᶻ

    PO-⊑ʸˣʸ = →-PO (PO-⊑ Y) (Y ⊎ X)
    DCPO-⊑ʸˣʸ = →-DCPO DCPO-⊑ʸ (Y ⊎ X)
    ωCPO-⊑ʸˣʸ = DCPO→ωCPO PO-⊑ʸˣʸ DCPO-⊑ʸˣʸ
    ⨆ʸˣʸ = ω-CompletePartialOrder.⨆ ωCPO-⊑ʸˣʸ

  open PartialOrder.PartialOrder PO-⊑ˣʸ using () renaming (≤-antisym to ⊑ˣʸ-antisym)
  open PartialOrder.PartialOrder PO-⊑ˣᶻ using () renaming (≤-antisym to ⊑ˣᶻ-antisym)
  open PartialOrder.PartialOrder PO-⊑ʸᶻ using () renaming (≤-antisym to ⊑ʸᶻ-antisym)

  open ω-CompletePartialOrder using (⨆-const) renaming (⨆-ub to ⨆-ub′; ⨆-lub to ⨆-lub′)
  open D-CompletePartialOrder using () renaming (⨆-ub to ⨆-ub′′; ⨆-lub to ⨆-lub′′)

  [η,]-mono : Mono PO-⊑ˣʸ PO-⊑ʸˣʸ [ η ,_]
  [η,]-mono g₁x⊑g₂x (inj₁ y) = ⊑-refl
  [η,]-mono g₁x⊑g₂x (inj₂ x) = g₁x⊑g₂x x

  [η,]-cont : ωCont ωCPO-⊑ˣʸ ωCPO-⊑ʸˣʸ ([ η ,_] ↑ [η,]-mono)
  [η,]-cont _ = →-≡ (λ { (inj₁ y) → D-CompletePartialOrder.⨆-const DCPO-⊑ʸ
                       ; (inj₂ x) → D-CompletePartialOrder.DirSeq-≡ DCPO-⊑ʸ refl})

  *-ωcontˡ : ∀ (f : X → L̅ Y) → ωCont ωCPO-⊑ʸᶻ ωCPO-⊑ˣᶻ ((_⋄ f) ↑ (*-monoˡ f))
  *-ωcontˡ f = Cont→ωCont {DCPO = DCPO-⊑ʸᶻ} {DCPO′ = DCPO-⊑ˣᶻ} ((_⋄ f) ↑ (*-monoˡ f)) (*-contˡ f) 
  
  *-ωcontʳ : ∀ (g : Y → L̅ Z) → ωCont ωCPO-⊑ˣʸ ωCPO-⊑ˣᶻ ((g ⋄_) ↑ (*-monoʳ g))
  *-ωcontʳ g = Cont→ωCont {DCPO = DCPO-⊑ˣʸ} {DCPO′ = DCPO-⊑ˣᶻ} (g ⋄_ ↑ *-monoʳ g) (*-contʳ g)

L̅-Iteration : ElgotIteration Kl-CoC
L̅-Iteration =
  record
    { _†  = λ {X} {Y} → _†
    ; fix = λ {X} {Y} {f} → fix f
    }
  where
    module _ {X Y : Set (ℓ ⊔ ℓ′)} (f : X → L̅ (Y ⊎ X)) where
      _⊑ʸ_ = _⊑_ Y
      DCPO-⊑ʸ = Complete-OM-Module.DCPO-⊑ (L̅-COMM Y)
      ωCPO-⊑ʸ = DCPO→ωCPO (PO-⊑ Y) DCPO-⊑ʸ 

      PO-⊑ˣʸ = →-PO (PO-⊑ Y) X
      DCPO-⊑ˣʸ = →-DCPO (Complete-OM-Module.DCPO-⊑ (L̅-COMM Y)) X
      ωCPO-⊑ˣʸ = DCPO→ωCPO PO-⊑ˣʸ DCPO-⊑ˣʸ
      ⨆ˣʸ = ω-CompletePartialOrder.⨆ ωCPO-⊑ˣʸ
    
      PO-⊑ʸˣʸ = →-PO (PO-⊑ Y) (Y ⊎ X)
      DCPO-⊑ʸˣʸ = →-DCPO DCPO-⊑ʸ (Y ⊎ X)
      ωCPO-⊑ʸˣʸ = DCPO→ωCPO PO-⊑ʸˣʸ DCPO-⊑ʸˣʸ
      ⨆ʸˣʸ = ω-CompletePartialOrder.⨆ ωCPO-⊑ʸˣʸ
      
      open ω-CompletePartialOrder using (⨆-const)
      open LeastFixpoints --{ωCPO = CPO-⊑ˣʸ}
      
      F : ContFun (ωCPO-⊑ˣʸ) (ωCPO-⊑ˣʸ)
      F = ωcont-∘ {ωCPO = ωCPO-⊑ˣʸ}{ωCPO′ = ωCPO-⊑ʸˣʸ} (([ η ,_] ↑ [η,]-mono {Z = Y ⊎ X}) ↝ [η,]-cont) (((_⋄ f) ↑ (*-monoˡ f)) ↝ (*-ωcontˡ f))

      _†  = μ F
      fix = μ-fix F

open Co-Cartesian.Co-Cartesian Kl-CoC using ([]-inl; []-inr; []-destruct)
  renaming (⊚-assoc to ⋄-assoc; ⊚-unitˡ to ⋄-unitˡ; ⊚-unitʳ to ⋄-unitʳ; ⊚-distrib-[] to ⋄-distrib-[])
open ElgotIteration.ElgotIteration L̅-Iteration
open LeastFixpoints

†-naturality : {X Y Z : Set (ℓ ⊔ ℓ′)} {f : X → L̅ (Y ⊎ X)} {g : Y → L̅ Z} → ([ (η ∘ inj₁) ⋄ g , η ∘ inj₂ ] ⋄ f) † ≡ g ⋄ f †
†-naturality {X}{Y}{Z}{f}{g} = sym $ μ-uni F G U (→-≡ UF≡GU) refl
    where
        ωCPO-⊑ʸ = DCPO→ωCPO (PO-⊑ Y) (Complete-OM-Module.DCPO-⊑ (L̅-COMM Y))

        PO-⊑ˣʸ = →-PO (PO-⊑ Y) X
        DCPO-⊑ˣʸ = →-DCPO (Complete-OM-Module.DCPO-⊑ (L̅-COMM Y)) X
        ωCPO-⊑ˣʸ = DCPO→ωCPO PO-⊑ˣʸ DCPO-⊑ˣʸ

        PO-⊑ˣᶻ = →-PO (PO-⊑ Z) X
        DCPO-⊑ˣᶻ = →-DCPO (Complete-OM-Module.DCPO-⊑ (L̅-COMM Z)) X
        ωCPO-⊑ˣᶻ = DCPO→ωCPO PO-⊑ˣᶻ DCPO-⊑ˣᶻ

        PO-⊑ʸˣʸ = →-PO (PO-⊑ Y) (Y ⊎ X)
        DCPO-⊑ʸˣʸ = →-DCPO (Complete-OM-Module.DCPO-⊑ (L̅-COMM Y)) (Y ⊎ X)
        ωCPO-⊑ʸˣʸ = DCPO→ωCPO PO-⊑ʸˣʸ DCPO-⊑ʸˣʸ

        PO-⊑ᶻˣᶻ = →-PO (PO-⊑ Z) (Z ⊎ X)
        DCPO-⊑ᶻˣᶻ = →-DCPO (Complete-OM-Module.DCPO-⊑ (L̅-COMM Z)) (Z ⊎ X)
        ωCPO-⊑ᶻˣᶻ = DCPO→ωCPO PO-⊑ᶻˣᶻ DCPO-⊑ᶻˣᶻ
    
        h = [ (η ∘ inj₁) ⋄ g , η ∘ inj₂ ] ⋄ f
        F = ωcont-∘ {ωCPO = ωCPO-⊑ˣʸ}{ωCPO′ = ωCPO-⊑ʸˣʸ} ([ η ,_] ↑ [η,]-mono ↝ [η,]-cont) (_⋄ f ↑ *-monoˡ f ↝ *-ωcontˡ f) 
        G = ωcont-∘ {ωCPO = ωCPO-⊑ˣᶻ}{ωCPO′ = ωCPO-⊑ᶻˣᶻ} ([ η ,_] ↑ [η,]-mono ↝ [η,]-cont) (_⋄ h ↑ *-monoˡ h ↝ *-ωcontˡ h)
        U = g ⋄_ ↑ *-monoʳ g ↝ *-ωcontʳ g

        UF≡GU : ∀ (u : X → L̅ Y) → g ⋄ ([ η , u ] ⋄ f) ≡ [ η , g ⋄ u ] ⋄ h
        UF≡GU u =
          begin
          g ⋄ ([ η , u ] ⋄ f ) 
               ≡⟨ ⋄-assoc {B = Y ⊎ X}{C = Y}{f = f} ⟩
          (g ⋄ [ η , u ]) ⋄ f
               ≡⟨ cong (_⋄ f) ⋄-distrib-[] ⟩
          [ g ⋄ η , g ⋄ u ] ⋄ f
               ≡⟨ cong (_⋄ f) (cong2 [_,_] (trans ⋄-unitʳ (sym ⋄-unitˡ)) refl) ⟩                      
          [ η ⋄ g , g ⋄ u ] ⋄ f 
               ≡˘⟨ cong (_⋄ f) (cong2 [_,_] (trans (⋄-assoc {f = g}) (cong (_⋄ g) ([]-inl {g = g ⋄ u }))) ([]-inr {f = η})) ⟩
          [ [ η , g ⋄ u ] ⋄ ((η ∘ inj₁) ⋄ g) , [ η , g ⋄ u ] ⋄ (η ∘ inj₂)] ⋄ f
               ≡˘⟨ cong (_⋄ f) ⋄-distrib-[] ⟩
          ([ η , g ⋄ u ] ⋄ [(η ∘ inj₁) ⋄ g , η ∘ inj₂ ]) ⋄ f
               ≡˘⟨ ⋄-assoc {f = f} ⟩
          [ η , g ⋄ u ] ⋄ ([(η ∘ inj₁) ⋄ g , η ∘ inj₂ ] ⋄ f)
          ∎

†-uniformity : {X Y Z : Set (ℓ ⊔ ℓ′)} {f : X → L̅ (Y ⊎ X)} {g : Z → L̅ (Y ⊎ Z)} {h : Z → X}
      → f ∘ h ≡ [ η ∘ inj₁ , (η ∘ inj₂) ∘ h ] ⋄ g  → f † ∘ h ≡ g †
†-uniformity {X}{Y}{Z}{f}{g}{h} fh≡[id+h]g = μ-uni F G U (→-≡ UF≡GU) refl
    where
      ωCPO-⊑ʸ = DCPO→ωCPO (PO-⊑ Y) (Complete-OM-Module.DCPO-⊑ (L̅-COMM Y))

      PO-⊑ˣʸ = →-PO (PO-⊑ Y) X
      DCPO-⊑ˣʸ = →-DCPO (Complete-OM-Module.DCPO-⊑ (L̅-COMM Y)) X
      ωCPO-⊑ˣʸ = DCPO→ωCPO PO-⊑ˣʸ DCPO-⊑ˣʸ

      PO-⊑ᶻʸ = →-PO (PO-⊑ Y) Z
      DCPO-⊑ᶻʸ = →-DCPO (Complete-OM-Module.DCPO-⊑ (L̅-COMM Y)) Z
      ωCPO-⊑ᶻʸ = DCPO→ωCPO PO-⊑ᶻʸ DCPO-⊑ᶻʸ

      PO-⊑ʸˣʸ = →-PO (PO-⊑ Y) (Y ⊎ X)
      DCPO-⊑ʸˣʸ = →-DCPO (Complete-OM-Module.DCPO-⊑ (L̅-COMM Y)) (Y ⊎ X)
      ωCPO-⊑ʸˣʸ = DCPO→ωCPO PO-⊑ʸˣʸ DCPO-⊑ʸˣʸ
      
      PO-⊑ʸᶻʸ = →-PO (PO-⊑ Y) (Y ⊎ Z)
      DCPO-⊑ʸᶻʸ = →-DCPO (Complete-OM-Module.DCPO-⊑ (L̅-COMM Y)) (Y ⊎ Z)
      ωCPO-⊑ʸᶻʸ = DCPO→ωCPO PO-⊑ʸᶻʸ DCPO-⊑ʸᶻʸ
        
      F = ωcont-∘ {ωCPO = ωCPO-⊑ˣʸ}{ωCPO′ = ωCPO-⊑ʸˣʸ} ([ η ,_] ↑ [η,]-mono {Z = Y ⊎ X} ↝ [η,]-cont) (_⋄ f ↑ *-monoˡ f ↝ *-ωcontˡ f) 
      G = ωcont-∘ {ωCPO = ωCPO-⊑ᶻʸ}{ωCPO′ = ωCPO-⊑ʸᶻʸ} ([ η ,_] ↑ [η,]-mono {Z = Y ⊎ Z} ↝ [η,]-cont) (_⋄ g ↑ *-monoˡ g ↝ *-ωcontˡ g) 
      U = _⋄ (η ∘ h) ↑ *-monoˡ (η ∘ h) ↝ *-ωcontˡ (η ∘ h)

      UF≡GU : ∀ (u : X → L̅ Y) → [ η , u ] ⋄ (f ∘ h) ≡ [ η , u ∘ h ] ⋄ g
      UF≡GU u =
        begin
        [ η , u ] ⋄ (f ∘ h)
             ≡⟨ cong ([ η , u ] ⋄_) fh≡[id+h]g ⟩
        [ η , u ] ⋄ (([ η ∘ inj₁ , (η ∘ inj₂) ∘ h ]) ⋄ g)
             ≡⟨ ⋄-assoc {f = g} ⟩
        ([ η , u ] ⋄ [ η ∘ inj₁ , (η ∘ inj₂) ∘ h ]) ⋄ g
             ≡⟨ cong (_⋄ g) ⋄-distrib-[] ⟩
        [ [ η , u ] ⋄ (η ∘ inj₁) , [ η , u ] ⋄ ((η ∘ inj₂) ∘ h) ] ⋄ g
             ≡⟨ cong (_⋄ g) (cong2 [_,_] ([]-inl {g = u}) ([]-inr {f = η})) ⟩
        [ η , u ∘ h ] ⋄ g
        ∎    

†-codiagonal : {X Y : Set (ℓ ⊔ ℓ′)} {f : X → L̅ ((Y ⊎ X) ⊎ X)} → ([ η , η ∘ inj₂ ] ⋄ f) † ≡ f † †
†-codiagonal {X}{Y}{f} =
  PartialOrder.≤-antisym PO-⊑ˣʸ
    (μ-lf F (f † †) ltr) (μ-lpf G (([ η , η ∘ inj₂ ] ⋄ f) †)
      (PartialOrder.≤-trans PO-⊑ˣʸ
        (PartialOrder.≡-to-≤ PO-⊑ˣʸ (sym (†-naturality {f = f} {g = [ η , ([ η , η ∘ inj₂ ] ⋄ f) † ]})))
         (μ-lf H (([ η , η ∘ inj₂ ] ⋄ f) †) rtl)))

    where
      ωCPO-⊑ʸ = DCPO→ωCPO (PO-⊑ Y) (Complete-OM-Module.DCPO-⊑ (L̅-COMM Y))

      PO-⊑ˣʸ = →-PO (PO-⊑ Y) X
      DCPO-⊑ˣʸ = →-DCPO (Complete-OM-Module.DCPO-⊑ (L̅-COMM Y)) X
      ωCPO-⊑ˣʸ = DCPO→ωCPO PO-⊑ˣʸ DCPO-⊑ˣʸ

      PO-⊑ʸˣʸ = →-PO (PO-⊑ Y) (Y ⊎ X)
      DCPO-⊑ʸˣʸ = →-DCPO (Complete-OM-Module.DCPO-⊑ (L̅-COMM Y)) (Y ⊎ X)
      ωCPO-⊑ʸˣʸ = DCPO→ωCPO PO-⊑ʸˣʸ DCPO-⊑ʸˣʸ
      
      F = ωcont-∘ {ωCPO = ωCPO-⊑ˣʸ}{ωCPO′ = ωCPO-⊑ʸˣʸ}
          ([ η ,_] ↑ [η,]-mono {Z = Y ⊎ X} ↝ [η,]-cont)
          (_⋄  ([ η , η ∘ inj₂ ] ⋄ f) ↑ *-monoˡ ([ η , η ∘ inj₂ ] ⋄ f ) ↝ *-ωcontˡ ([ η , η ∘ inj₂ ] ⋄ f))

      G = ωcont-∘ {ωCPO = ωCPO-⊑ˣʸ}{ωCPO′ = ωCPO-⊑ʸˣʸ}
          ([ η ,_] ↑ [η,]-mono {Z = Y ⊎ X} ↝ [η,]-cont)
          (_⋄  (f †) ↑ *-monoˡ (f †) ↝ *-ωcontˡ (f †))

      H = ωcont-∘ {ωCPO = ωCPO-⊑ˣʸ}{ωCPO′ = ωCPO-⊑ʸˣʸ}
          ([ η ,_] ↑ [η,]-mono {Z = Y ⊎ X} ↝ [η,]-cont)
          (_⋄ ([ (η ∘ inj₁) ⋄ [ η , ([ η , η ∘ inj₂ ] ⋄ f) † ] , η ∘ inj₂ ] ⋄ f)
            ↑  *-monoˡ ([ (η ∘ inj₁)  ⋄ [ η , ([ η , η ∘ inj₂ ] ⋄ f) † ] , η ∘ inj₂ ] ⋄ f)
            ↝ *-ωcontˡ ([ (η ∘ inj₁) ⋄ [ η , ([ η , η ∘ inj₂ ] ⋄ f) † ] , η ∘ inj₂ ] ⋄ f))

      ltr : [ η , f † † ] ⋄ ([ η , η ∘ inj₂ ] ⋄ f) ≡ f † †
      ltr =
        begin
        [ η , f † † ] ⋄ ([ η , η ∘ inj₂ ] ⋄ f)
             ≡⟨ ⋄-assoc {f = f} ⟩
        ([ η , f † † ] ⋄ [ η , η ∘ inj₂ ]) ⋄ f
             ≡⟨ cong (_⋄ f) ⋄-distrib-[] ⟩
        [ [ η , f † † ] ⋄ η , [ η , f † † ] ⋄ η ∘ inj₂ ] ⋄ f
             ≡⟨ cong (_⋄ f) ([]-destruct refl ([]-inr {f = η})) ⟩
        [ [ η , f † † ] ⋄ η , f † † ] ⋄ f
             ≡˘⟨ cong (_⋄ f) ([]-destruct refl (fix {f = f †})) ⟩
        [ [ η , f † † ] ⋄ η , [ η , f † † ] ⋄ f † ] ⋄ f
             ≡˘⟨ cong (_⋄ f) ⋄-distrib-[] ⟩
        ([ η , f † † ] ⋄ [ η , f † ]) ⋄ f
             ≡˘⟨ ⋄-assoc {f = f} ⟩
        [ η , f † † ] ⋄ ([ η , f † ] ⋄ f)
             ≡⟨ cong (_⋄_ [ η , f † † ]) (fix {f = f}) ⟩
        [ η , f † † ] ⋄ f †
             ≡⟨ fix {f = f †} ⟩
        f † †
        ∎
        
      rtl : [ η , ([ η , η ∘ inj₂ ] ⋄ f) † ] ⋄ ([ (η ∘ inj₁) ⋄ [ η , ([ η , η ∘ inj₂ ] ⋄ f) † ] , η ∘ inj₂ ] ⋄ f) ≡ ([ η , η ∘ inj₂ ] ⋄ f) †
      rtl =
        begin
        [ η , ([ η , η ∘ inj₂ ] ⋄ f) † ] ⋄ ([ (η ∘ inj₁) ⋄ [ η , ([ η , η ∘ inj₂ ] ⋄ f) † ] , η ∘ inj₂ ] ⋄ f)
             ≡⟨ ⋄-assoc {f = f} ⟩
        ([ η , ([ η , η ∘ inj₂ ] ⋄ f) † ] ⋄ [ (η ∘ inj₁) ⋄ [ η , ([ η , η ∘ inj₂ ] ⋄ f) † ] , η ∘ inj₂ ]) ⋄ f
             ≡⟨ cong (_⋄ f) ⋄-distrib-[] ⟩
        [ [ η , ([ η , η ∘ inj₂ ] ⋄ f) † ] ⋄ ((η ∘ inj₁) ⋄ [ η , ([ η , η ∘ inj₂ ] ⋄ f) † ]) , [ η , ([ η , η ∘ inj₂ ] ⋄ f) † ] ⋄ (η ∘ inj₂) ] ⋄ f
             ≡⟨ cong (_⋄ f) $ []-destruct (⋄-assoc {f = [ η , ([ η , η ∘ inj₂ ] ⋄ f) † ]}) ([]-inr {f = η}) ⟩
        [ ([ η , ([ η , η ∘ inj₂ ] ⋄ f) † ] ⋄ (η ∘ inj₁)) ⋄ [ η , ([ η , η ∘ inj₂ ] ⋄ f) † ] ,  ([ η , η ∘ inj₂ ] ⋄ f) † ] ⋄ f               
             ≡⟨ cong (λ w → [ w ⋄ [ η , ([ η , η ∘ inj₂ ] ⋄ f) † ] ,  ([ η , η ∘ inj₂ ] ⋄ f) † ] ⋄ f) ([]-inl {g = ([ η , η ∘ inj₂ ] ⋄ f) † }) ⟩
        [ ([ η , ([ η , η ∘ inj₂ ] ⋄ f) † ] ⋄ (η ∘ inj₁)) ⋄ [ η , ([ η , η ∘ inj₂ ] ⋄ f) † ] ,  ([ η , η ∘ inj₂ ] ⋄ f) † ] ⋄ f               
             ≡⟨ cong (λ w → [ w ,  ([ η , η ∘ inj₂ ] ⋄ f) † ] ⋄ f) ⋄-unitˡ ⟩
        [ [ η , ([ η , η ∘ inj₂ ] ⋄ f) † ] , ([ η , η ∘ inj₂ ] ⋄ f) † ] ⋄ f               
             ≡˘⟨ cong (_⋄ f) ([]-destruct ⋄-unitʳ ([]-inr {f = η})) ⟩
        [ [ η , ([ η , η ∘ inj₂ ] ⋄ f) † ] ⋄ η , [ η , ([ η , η ∘ inj₂ ] ⋄ f) † ] ⋄ η ∘ inj₂ ] ⋄ f
             ≡˘⟨ cong (_⋄ f) ⋄-distrib-[] ⟩
        ([ η , ([ η , η ∘ inj₂ ] ⋄ f) † ] ⋄ [ η , η ∘ inj₂ ]) ⋄ f
             ≡˘⟨ ⋄-assoc {f = f} ⟩
        [ η , ([ η , η ∘ inj₂ ] ⋄ f) † ] ⋄ ([ η , η ∘ inj₂ ] ⋄ f)
             ≡⟨ fix {f = [ η , η ∘ inj₂ ] ⋄ f } ⟩
        ([ η , η ∘ inj₂ ] ⋄ f) †
        ∎                    

-- L̅ is an Elgot monad
L̅-UniConway : TotalUniConway Kl-CoC L̅-Iteration CoC-C→Kl
L̅-UniConway =
   record
     { nat = λ {X} {Y} {Z} {f} {g} → †-naturality {X}{Y}{Z}{f}{g}
     ; uni = λ {X} {Y} {Z} {f} {g} {h} → †-uniformity {X}{Y}{Z}{f}{g}{h}
     ; cod = λ {X} {Y} {f} → †-codiagonal {X} {Y} {f} 
   }
