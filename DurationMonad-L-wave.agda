{-# OPTIONS --cubical --safe #-}

open import Level using (Level; _⊔_) renaming (suc to ℓ-suc)
open import Function using (id; _∘_; _$_)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (_⊎_; inj₁; inj₂; [_,_])
open import Data.Product using (_,_; proj₁; proj₂)
open import Data.Nat using (ℕ; zero; suc)
                     renaming (_⊔_ to _⊔ᴺ_; _+_ to _+ᴺ_; _≤_ to _≤ᴺ_; z≤n to z≤ᴺn; s≤s to s≤ᴺs; ≤-pred to ≤ᴺ-pred)
open import Data.Nat.Properties using (m≤m⊔n; n≤m⊔n; +-suc; +-identityʳ; _≤?_)


open import CubicalIdentity using (_≡_; refl; sym; cong; trans; →-≡)
open CubicalIdentity.≡-Reasoning

open import Category
open import Co-Cartesian
open import Monoid
open import MonoidModule
open import Kleisli
open import ElgotIteration
open import PartialOrder
open import CompletePartialOrder

import Eliminators-L-wave

--*
{-
  This module defines the duration monad L̃ by initiality of L̃.
-}
--*

module DurationMonad-L-wave {ℓ ℓ′ : Level} {M : Monoid} (OM : O-Monoid {ℓ} {ℓ′} M) where

open Eliminators-L-wave OM
open Def-L̃

open DirSeq

L̃-DurationMonad : Kleisli L̃
L̃-DurationMonad =
  record
    { ηₓ = η
    ; _* = λ {X} {Y} f → fun (H (L̃-Initial X) (L̃*-COMMo f))
    ; ηₓ-unitˡ = λ {X} → uniq (L̃-Initial X) COMMMo-id
    ; ηₓ-unitʳ = λ {X} {Y} {f} → f-η (H (L̃-Initial X) (L̃*-COMMo f))
    ; *-assoc = λ {X} {Y} {Z} {f} {g} → uniq (L̃-Initial X) ((G′ f g) COMMMo-∘ H (L̃-Initial X) (L̃*-COMMo f))
    }
  where
    open Complete-OM-Module-Morphism-over using (COMMM; fun; f-η)
    open Initial-Complete-OM-Module-over using (H; uniq)
    module _ {X Y Z : Set (ℓ ⊔ ℓ′)} (f : X → L̃ Y) (g : Y → L̃ Z) where
      G : Complete-OM-Module-Morphism-over (L̃-COMMo Y) (L̃*-COMMo g)
      G = H (L̃-Initial Y) (L̃*-COMMo g)
      G′ : Complete-OM-Module-Morphism-over (L̃*-COMMo f) (L̃*-COMMo ((fun G) ∘ f))
      G′ = record
             { COMMM = COMMM G
             ; f-η = refl
             }

open Kleisli.Kleisli L̃-DurationMonad

module _ {X Y Z : Set (ℓ ⊔ ℓ′)} where

  open Complete-OM-Module-Morphism-over using (f-⊑; f-⨆; f-η)
  open Initial-Complete-OM-Module-over using (H; uniq)

  private
    _⊑ʸ_ = _⊑_ Y
    _⊑ᶻ_ = _⊑_ Z

    PO-⊑ˣʸ = →-PO (PO-⊑ Y) X
    DCPO-⊑ˣʸ = →-DCPO (Complete-OM-Module.DCPO-⊑ (L̃-COMM Y)) X
    ⨆ˣʸ = D-CompletePartialOrder.⨆ DCPO-⊑ˣʸ
    PO-⊑ˣᶻ = →-PO (PO-⊑ Z) X
    DCPO-⊑ˣᶻ = →-DCPO (Complete-OM-Module.DCPO-⊑ (L̃-COMM Z)) X
    ⨆ˣᶻ = D-CompletePartialOrder.⨆ DCPO-⊑ˣᶻ
    PO-⊑ʸᶻ = →-PO (PO-⊑ Z) Y
    DCPO-⊑ʸᶻ = →-DCPO (Complete-OM-Module.DCPO-⊑ (L̃-COMM Z)) Y
    ⨆ʸᶻ = D-CompletePartialOrder.⨆ DCPO-⊑ʸᶻ
    PO-⊑ʸ*ᶻ = →-PO (PO-⊑ Z) (L̃ Y)
    DCPO-⊑ʸ*ᶻ = →-DCPO (Complete-OM-Module.DCPO-⊑ (L̃-COMM Z)) (L̃ Y)
    ⨆ʸ*ᶻ = D-CompletePartialOrder.⨆ DCPO-⊑ʸ*ᶻ

  *-monoˡ′ : Mono PO-⊑ʸᶻ (→-PO (PO-⊑ Z) (L̃ Y)) (_*)
  *-monoˡ′ {g₁} {g₂} g₁x⊑g₂x = L̃-rec
    where
      args : Arguments Y
      args = record
               { P-L̃ = λ x → (g₁ *) x ⊑ᶻ (g₂ *) x
               ; P-⊑ = λ _ _ _ → ⊤
               ; P-▷ = λ a → ▷-monoʳ
               ; P-⊥ = ⊑-refl
               ; P-⨆ = λ { (p-seq , p-inc) → ⨆-lub (λ n → ⊑-trans (p-seq n) (⨆-ub n)) }
               ; P-η = g₁x⊑g₂x
               ; P-⊑-antisym = λ px py _ _ → ⊑-prop _ _
               ; P-⊑-prop = λ { _ _ tt tt → refl }
               }
      elims : Eliminators Y args
      elims = L̃-Elim Y args
      open Eliminators elims using (L̃-rec) public

  *-monoˡ : ∀ (f : X → L̃ Y) → Mono PO-⊑ʸᶻ PO-⊑ˣᶻ (_⋄ f)
  *-monoˡ f g₁x⊑g₂x x = *-monoˡ′ g₁x⊑g₂x (f x)

  *-monoʳ : ∀ (g : Y → L̃ Z) → Mono PO-⊑ˣʸ PO-⊑ˣᶻ (g ⋄_) 
  *-monoʳ g f₁x⊑f₂x x = f-⊑ (H (L̃-Initial Y) (L̃*-COMMo g)) (f₁x⊑f₂x x)

  *-contˡ′ : Cont DCPO-⊑ʸᶻ (→-DCPO (Complete-OM-Module.DCPO-⊑ (L̃-COMM Z)) (L̃ Y)) (_* ↑  *-monoˡ′)
  *-contˡ′ (seq ⇗ dir) = sym (uniq (L̃-Initial Y) h')
    where
      open D-CompletePartialOrder (Complete-OM-Module.DCPO-⊑ (L̃-COMM Z))
           renaming (⊑-antisym to ⊑ᶻ-antisym; ⊑-trans to ⊑ᶻ-trans; ⨆ to ⨆ᶻ;
             ⨆-ub to ⨆ᶻ-ub; ⨆-lub to ⨆ᶻ-lub; ⨆-const to ⨆ᶻ-const)

      h : Complete-OM-Module-Morphism (L̃-COMM Y) (L̃-COMM Z)   
      h = record
            { fun = λ x → ⨆ᶻ (DirSeq-mono { PO = PO-⊑ʸᶻ} (seq ⇗ dir) ((λ h → (h *) x) ↑ (λ h → *-monoˡ′ h x)))
            ; f-⊑ = λ x⊑y → ⨆ᶻ-lub (λ n → ⊑ᶻ-trans (f-⊑ (H (L̃-Initial Y) (L̃*-COMMo (seq n))) x⊑y) (⨆ᶻ-ub n))
            ; f-⊥ = ⨆ᶻ-const 
            ; f-▷ = Complete-OM-Module.▷-contʳ (L̃-COMM Z) 
            ; f-⨆ = ⊑ᶻ-antisym (⨆ᶻ-lub (λ n → ⨆ᶻ-lub (λ m → ⊑ᶻ-trans (⨆ᶻ-ub n) (⨆ᶻ-ub m))))
                              (⨆ᶻ-lub (λ n → ⨆ᶻ-lub (λ m → ⊑ᶻ-trans (⨆ᶻ-ub n) (⨆ᶻ-ub m))))
            }
  
      h' : Complete-OM-Module-Morphism-over (L̃-COMMo Y) (record { η = ⨆ʸᶻ (seq ⇗ dir) }) 
      h' = record
             { COMMM = h
             ; f-η = →-≡ (λ x → ⊑ᶻ-antisym (⨆-lub (λ n → ⨆-ub n)) (⨆-lub (λ n → ⨆-ub n)))
             }
  
  *-contˡ : ∀ (f : X → L̃ Y) → Cont DCPO-⊑ʸᶻ DCPO-⊑ˣᶻ (_⋄ f ↑ *-monoˡ f)
  *-contˡ f s = →-≡ (λ x → (cong (λ k → k (f x)) (*-contˡ′ s)))

  *-contʳ : ∀ (g : Y → L̃ Z) → Cont DCPO-⊑ˣʸ DCPO-⊑ˣᶻ (g ⋄_ ↑ *-monoʳ g)
  *-contʳ g (seq ⇗ dir) = →-≡ (λ x → sym (f-⨆ (H (L̃-Initial Y) (L̃*-COMMo g))
                                                 {s =  (λ n → seq n x) ⇗ λ n m →
                                                            (proj₁ $ dir n m) , 
                                                            (proj₁ $ proj₂ $ dir n m) x ,
                                                            (proj₂ $ proj₂ $ dir n m) x
                                                  })) 

  *-⊥ : ∀ {f : X → L̃ Y} → (f *) ⊥ ≡ ⊥
  *-⊥ = refl

module _ {X Y Z : Set (ℓ ⊔ ℓ′)} where

  private 
    _⊑ʸ_ = _⊑_ Y
    DCPO-⊑ʸ = Complete-OM-Module.DCPO-⊑ (L̃-COMM Y)
    ωCPO-⊑ʸ = DCPO→ωCPO (PO-⊑ Y) DCPO-⊑ʸ 

    _⊑ᶻ_ = _⊑_ Z
    ωCPO-⊑ᶻ = DCPO→ωCPO (PO-⊑ Z) (Complete-OM-Module.DCPO-⊑ (L̃-COMM Z))
    
    PO-⊑ˣʸ = →-PO (PO-⊑ Y) X
    DCPO-⊑ˣʸ = →-DCPO (Complete-OM-Module.DCPO-⊑ (L̃-COMM Y)) X
    ωCPO-⊑ˣʸ = DCPO→ωCPO PO-⊑ˣʸ DCPO-⊑ˣʸ
    ⨆ˣʸ = ω-CompletePartialOrder.⨆ ωCPO-⊑ˣʸ
                                   
    PO-⊑ˣᶻ = →-PO (PO-⊑ Z) X
    DCPO-⊑ˣᶻ = →-DCPO (Complete-OM-Module.DCPO-⊑ (L̃-COMM Z)) X
    ωCPO-⊑ˣᶻ = DCPO→ωCPO PO-⊑ˣᶻ DCPO-⊑ˣᶻ
    _⊑ˣᶻ_ = ω-CompletePartialOrder._⊑_ ωCPO-⊑ˣᶻ
    ⨆ˣᶻ = ω-CompletePartialOrder.⨆ ωCPO-⊑ˣᶻ
    
    PO-⊑ʸᶻ = →-PO (PO-⊑ Z) Y
    DCPO-⊑ʸᶻ = →-DCPO (Complete-OM-Module.DCPO-⊑ (L̃-COMM Z)) Y
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

  *-ωcontˡ : ∀ (f : X → L̃ Y) → ωCont ωCPO-⊑ʸᶻ ωCPO-⊑ˣᶻ ((_⋄ f) ↑ (*-monoˡ f))
  *-ωcontˡ f = Cont→ωCont {DCPO = DCPO-⊑ʸᶻ} {DCPO′ = DCPO-⊑ˣᶻ} ((_⋄ f) ↑ (*-monoˡ f)) (*-contˡ f) 
  
  *-ωcontʳ : ∀ (g : Y → L̃ Z) → ωCont ωCPO-⊑ˣʸ ωCPO-⊑ˣᶻ ((g ⋄_) ↑ (*-monoʳ g))
  *-ωcontʳ g = Cont→ωCont {DCPO = DCPO-⊑ˣʸ} {DCPO′ = DCPO-⊑ˣᶻ} (g ⋄_ ↑ *-monoʳ g) (*-contʳ g)

L̃-Iteration : ElgotIteration Kl-CoC
L̃-Iteration =
  record
    { _†  = λ {X} {Y} → _† {Z = Y ⊎ X}
    ; fix = λ {X} {Y} {f} → fix {Z = Y ⊎ X} f
    }
  where
    module _ {X Y Z : Set (ℓ ⊔ ℓ′)} (f : X → L̃ (Y ⊎ X)) where
      _⊑ʸ_ = _⊑_ Y
      DCPO-⊑ʸ = Complete-OM-Module.DCPO-⊑ (L̃-COMM Y)
      ωCPO-⊑ʸ = DCPO→ωCPO (PO-⊑ Y) DCPO-⊑ʸ 

      PO-⊑ˣʸ = →-PO (PO-⊑ Y) X
      DCPO-⊑ˣʸ = →-DCPO (Complete-OM-Module.DCPO-⊑ (L̃-COMM Y)) X
      ωCPO-⊑ˣʸ = DCPO→ωCPO PO-⊑ˣʸ DCPO-⊑ˣʸ
      ⨆ˣʸ = ω-CompletePartialOrder.⨆ ωCPO-⊑ˣʸ

      PO-⊑ʸᶻ = →-PO (PO-⊑ Z) Y
      DCPO-⊑ʸᶻ = →-DCPO (Complete-OM-Module.DCPO-⊑ (L̃-COMM Z)) Y
      ωCPO-⊑ʸᶻ = DCPO→ωCPO PO-⊑ʸᶻ DCPO-⊑ʸᶻ
      ⨆ʸᶻ = ω-CompletePartialOrder.⨆ ωCPO-⊑ʸᶻ
    
      PO-⊑ʸˣʸ = →-PO (PO-⊑ Y) (Y ⊎ X)
      DCPO-⊑ʸˣʸ = →-DCPO DCPO-⊑ʸ (Y ⊎ X)
      ωCPO-⊑ʸˣʸ = DCPO→ωCPO PO-⊑ʸˣʸ DCPO-⊑ʸˣʸ
      ⨆ʸˣʸ = ω-CompletePartialOrder.⨆ ωCPO-⊑ʸˣʸ
      
      open ω-CompletePartialOrder using (⨆-const)
      open LeastFixpoints ωCPO-⊑ˣʸ
      
      F : ContFun (ωCPO-⊑ˣʸ) (ωCPO-⊑ˣʸ)
      F = (λ g → [ η , g ] ⋄ f)
          ↑ (λ {g₁} {g₂} g₁x⊑g₂x → *-monoˡ f ([η,]-mono {Z = Z} g₁x⊑g₂x)) 
          ↝ λ { s@(seq ↗ inc) → 
                 begin
                   ⨆ˣʸ ((λ n → ([ η , seq n ] ⋄ f)) ↗ ((*-monoˡ f) ∘ [η,]-mono ∘ inc))
                 ≡⟨ *-ωcontˡ f ((λ n → [ η , seq n ]) ↗ [η,]-mono ∘ inc) ⟩                
                   ⨆ʸˣʸ ((λ n → [ η , seq n ]) ↗ ([η,]-mono ∘ inc)) ⋄ f
                 ≡⟨ cong (_⋄ f) ([η,]-cont s) ⟩
                   [ η , ⨆ˣʸ s ] ⋄ f 
                 ∎ } 
      _†  = μ F
      fix = μ-fix F

{-
--open TotalUniConway
--open Co-Cartesian.Co-Cartesian Kl-CoC renaming (_⊚_ to _⋄_) hiding ([_,_])
open ElgotIteration.ElgotIteration L̃-Iteration


L̃-UniConway : TotalUniConway Kl-CoC L̃-Iteration CoC-C→Kl
L̃-UniConway =
   record
     { nat = λ {X} {Y} {Z} {f} {g} →
           let
             ωCPO-⊑ʸ = DCPO→ωCPO (PO-⊑ Y) (Complete-OM-Module.DCPO-⊑ (L̃-COMM Y))
             ωCPO-⊑ʸˣ = →-ωCPO ωCPO-⊑ʸ X in
             begin
             ([((η ∘ inj₁) ⋄ g) , ((η ∘ inj₂) ⋄ η) ] ⋄ f) † 
               ≡⟨ {!!} ⟩
             {!!}
               ≡⟨ *-ωcontʳ g {!!} ⟩
             g ⋄ (f †) 
             ∎
            
             --  trans {! (trans (*-ωcontˡ ([ (η ∘ inj₁) ⋄ g , (η ∘ inj₂) ⋄ η ] ⋄ f) ) (cong (λ k → k ⋄  ([ (η ∘ inj₁) ⋄ g , (η ∘ inj₂) ⋄ η ] ⋄ f) ) [η,]-cont))!} {!!}
       -- trans (*-ωcontʳ g) (cong (g ⋄_) (ω-CompletePartialOrder.⨆-eq ωCPO-⊑ʸˣ (→-≡ (λ n →  →-≡ (λ x → {!!}))) ) )
     ; cod = {!!}
     ; uni = {!!}
     }

-}
