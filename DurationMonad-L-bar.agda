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

open import Monoid
open import MonoidModule
open import Kleisli
open import ElgotIteration
open import PartialOrder
open import CompletePartialOrder

import Eliminators-L-bar

--*
{-
  This module defines the duration monad L̅ by initiality of L̅.
-}
--*

module DurationMonad-L-bar {ℓ : Level} {M : Monoid} (OM : O-Monoid {ℓ} {ℓ} M) where

open Eliminators-L-bar OM
open Def-L̅

open DirSeq

L̅-DurationMonad : Kleisli L̅
L̅-DurationMonad =
  record
    { ηₓ = η
    ; _* = λ {X} {Y} f → fun (H (L̅-Initial X) (L̅*-CCOMMo f))
    ; ηₓ-unitˡ = λ {X} → uniq (L̅-Initial X) {CCOMMo′ = L̅-CCOMMo X} COMMMo-id
    ; ηₓ-unitʳ = λ {X} {Y} {f} → f-η (H (L̅-Initial X) (L̅*-CCOMMo f))
    ; *-assoc = λ {X} {Y} {Z} {f} {g} → uniq (L̅-Initial X) {CCOMMo′ = L̅*-CCOMMo ((fun (G f g)) ∘ f)}
                                             ((G′ f g) COMMMo-∘ H (L̅-Initial X) (L̅*-CCOMMo f))
    }
  where
    open Complete-OM-Module-Morphism-over using (COMMM; fun; f-η)
    open Initial-C-Complete-OM-Module-over using (H; uniq)
    module _ {X Y Z : Set ℓ} (f : X → L̅ Y) (g : Y → L̅ Z) where
      G : C-Complete-OM-Module-Morphism-over (L̅-CCOMMo Y) (L̅*-CCOMMo g)
      G = H (L̅-Initial Y) (L̅*-CCOMMo g)
      G′ : C-Complete-OM-Module-Morphism-over (L̅*-CCOMMo f) (L̅*-CCOMMo ((fun G) ∘ f))
      G′ = record
             { COMMM = COMMM G
             ; f-η = refl
             }

open Kleisli.Kleisli L̅-DurationMonad


module _ {X Y Z : Set ℓ} where

  open Complete-OM-Module-Morphism-over using (f-⊑; f-⨆; f-η)
  open Initial-C-Complete-OM-Module-over using (H; uniq)

  private
    _⊑ʸ_ = _⊑_ Y
    _⊑ᶻ_ = _⊑_ Z

    PO-⊑ˣʸ = →-PO (PO-⊑ Y) X
    DCPO-⊑ˣʸ = →-DCPO ((Complete-OM-Module.DCPO-⊑ (L̅-COMM Y))) X
    ⨆ˣʸ = D-CompletePartialOrder.⨆ DCPO-⊑ˣʸ
    PO-⊑ˣᶻ = →-PO (PO-⊑ Z) X
    DCPO-⊑ˣᶻ = →-DCPO ( (Complete-OM-Module.DCPO-⊑ (L̅-COMM Z))) X
    ⨆ˣᶻ = D-CompletePartialOrder.⨆ DCPO-⊑ˣᶻ
    PO-⊑ʸᶻ = →-PO (PO-⊑ Z) Y
    DCPO-⊑ʸᶻ = →-DCPO ( (Complete-OM-Module.DCPO-⊑ (L̅-COMM Z))) Y
    ⨆ʸᶻ = D-CompletePartialOrder.⨆ DCPO-⊑ʸᶻ
    PO-⊑ʸ*ᶻ = →-PO (PO-⊑ Z) (L̅ Y)
    DCPO-⊑ʸ*ᶻ = →-DCPO ( (Complete-OM-Module.DCPO-⊑ (L̅-COMM Z))) (L̅ Y)
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
  *-monoʳ g f₁x⊑f₂x x = f-⊑ (H (L̅-Initial Y) (L̅*-CCOMMo g)) (f₁x⊑f₂x x)

  *-contˡ′ : Cont DCPO-⊑ʸᶻ (→-DCPO (Complete-OM-Module.DCPO-⊑ (L̅-COMM Z)) (L̅ Y)) (_* ↑  *-monoˡ′)
  *-contˡ′ (seq ⇗ dir) = sym (uniq (L̅-Initial Y) {CCOMMo′ = L̅-CCOMMoYZ} h′)
    where
      open D-CompletePartialOrder (Complete-OM-Module.DCPO-⊑ (L̅-COMM Z))
           renaming (⊑-antisym to ⊑ᶻ-antisym; ⊑-trans to ⊑ᶻ-trans; ⨆ to ⨆ᶻ; ⨆-ub to ⨆ᶻ-ub; ⨆-lub to ⨆ᶻ-lub; ⨆-const to ⨆ᶻ-const)

      h : C-Complete-OM-Module-Morphism (L̅-CCOMM Y) (L̅-CCOMM Z)   
      h = record
            { fun = λ x → ⨆ᶻ (DirSeq-mono { PO = PO-⊑ʸᶻ} (seq ⇗ dir) ((λ h → (h *) x) ↑ (λ h → *-monoˡ′ h x)))
            ; f-⊑ = λ x⊑y → ⨆ᶻ-lub (λ n → ⊑ᶻ-trans (f-⊑ (H (L̅-Initial Y) (L̅*-CCOMMo (seq n))) x⊑y)
                                                   (⨆ᶻ-ub n))
            ; f-⊥ = ⨆ᶻ-const 
            ; f-▷ = Complete-OM-Module.▷-contʳ (L̅-COMM Z)
            ; f-⨆ = ⊑ᶻ-antisym (⨆ᶻ-lub (λ n → ⨆ᶻ-lub (λ m → ⊑ᶻ-trans (⨆ᶻ-ub n) (⨆ᶻ-ub m))))
                                (⨆ᶻ-lub (λ n → ⨆ᶻ-lub (λ m → ⊑ᶻ-trans (⨆ᶻ-ub n) (⨆ᶻ-ub m))))
            }
      L̅-CCOMMoYZ : C-Complete-OM-Module-over Y OM (L̅-CCOMM Z)
      L̅-CCOMMoYZ = record { η = ⨆ʸᶻ (seq ⇗ dir) }
      h′ : C-Complete-OM-Module-Morphism-over (L̅-CCOMMo Y) (L̅-CCOMMoYZ) 
      h′ = record
             { COMMM = h
             ; f-η = →-≡ (λ x → ⊑ᶻ-antisym (⨆-lub (λ n → ⨆-ub n))
                                           (⨆-lub (λ n → ⨆-ub n)))
             }

  *-contˡ : ∀ (f : X → L̅ Y) → Cont DCPO-⊑ʸᶻ DCPO-⊑ˣᶻ (_⋄ f ↑  *-monoˡ f)
  *-contˡ f s = →-≡ (λ x → (cong (λ k → k (f x)) (*-contˡ′ s)))

  *-contʳ : ∀ (g : Y → L̅ Z) → Cont DCPO-⊑ˣʸ DCPO-⊑ˣᶻ (g ⋄_ ↑  *-monoʳ g)
  *-contʳ g (seq ⇗ dir) = →-≡ (λ x → sym (f-⨆ (H (L̅-Initial Y) (L̅*-CCOMMo g))
                                                  {s =  (λ n → seq n x) ⇗ λ n m → (proj₁ $ dir n m)
                                                                                , (proj₁ $ proj₂ $ dir n m) x
                                                                                , (proj₂ $ proj₂ $ dir n m) x})) 

  *-⊥ : ∀ {f : X → L̅ Y} → (f *) ⊥ ≡ ⊥
  *-⊥ = refl

module _ {X Y Z : Set ℓ} where

  private 
    _⊑ʸ_ = _⊑_ Y
    ωCPO-⊑ʸ = DCPO→ωCPO (PO-⊑ Y) (Complete-OM-Module.DCPO-⊑ (L̅-COMM Y))

    _⊑ᶻ_ = _⊑_ Z
    ωCPO-⊑ᶻ = DCPO→ωCPO (PO-⊑ Z) (Complete-OM-Module.DCPO-⊑ (L̅-COMM Z))
    
    PO-⊑ˣʸ = →-PO (PO-⊑ Y) X
    ωCPO-⊑ˣʸ = →-ωCPO ωCPO-⊑ʸ X
    ⨆ˣʸ = ω-CompletePartialOrder.⨆ ωCPO-⊑ˣʸ
                                   
    PO-⊑ˣᶻ = →-PO (PO-⊑ Z) X
    ωCPO-⊑ˣᶻ = →-ωCPO ωCPO-⊑ᶻ X
    _⊑ˣᶻ_ = ω-CompletePartialOrder._⊑_ ωCPO-⊑ˣᶻ
    ⨆ˣᶻ = ω-CompletePartialOrder.⨆ ωCPO-⊑ˣᶻ
    
    PO-⊑ʸᶻ = →-PO (PO-⊑ Z) Y
    ωCPO-⊑ʸᶻ = →-ωCPO ωCPO-⊑ᶻ Y
    ⨆ʸᶻ = ω-CompletePartialOrder.⨆ ωCPO-⊑ʸᶻ

  open PartialOrder.PartialOrder PO-⊑ˣʸ using () renaming (≤-antisym to ⊑ˣʸ-antisym)
  open PartialOrder.PartialOrder PO-⊑ˣᶻ using () renaming (≤-antisym to ⊑ˣᶻ-antisym)
  open PartialOrder.PartialOrder PO-⊑ʸᶻ using () renaming (≤-antisym to ⊑ʸᶻ-antisym)

  open ω-CompletePartialOrder using (⨆-const) renaming (⨆-ub to ⨆-ub′; ⨆-lub to ⨆-lub′)
  open D-CompletePartialOrder using () renaming (⨆-ub to ⨆-ub′′; ⨆-lub to ⨆-lub′′)

  *-ωcontˡ : ∀ (f : X → L̅ Y) → ωCont ωCPO-⊑ʸᶻ ωCPO-⊑ˣᶻ ((_⋄ f) ↑ (*-monoˡ f))
  *-ωcontˡ f (seq ↗ inc) = trans (trans (⊑ˣᶻ-antisym (⨆-lub′ ωCPO-⊑ˣᶻ
                                                             (λ n x → ⨆-ub n))
                                                     (⨆-lub′′ (→-DCPO (Complete-OM-Module.DCPO-⊑ (L̅-COMM Z)) X)
                                                              (λ n x → ⨆-ub n)))
                                        (*-contˡ f (seq ⇗ (λ m n →  n ⊔ᴺ m 
                                                          , (IncSeq-trans {PO = PO-⊑ʸᶻ} (seq ↗ inc) m (n ⊔ᴺ m) (n≤m⊔n n m))
                                                          , (IncSeq-trans {PO = PO-⊑ʸᶻ } (seq ↗ inc) n (n ⊔ᴺ m) (m≤m⊔n n m)) )) ))
                                        (cong (_⋄ f)
                                              (⊑ʸᶻ-antisym (⨆-lub′′ (→-DCPO (Complete-OM-Module.DCPO-⊑ (L̅-COMM Z)) Y)
                                                                    (λ n x → ⨆-ub n))
                                                           (⨆-lub′ ωCPO-⊑ʸᶻ
                                                                   (λ n x → ⨆-ub n))))

  *-ωcontʳ : ∀ (g : Y → L̅ Z) → ωCont ωCPO-⊑ˣʸ ωCPO-⊑ˣᶻ ((g ⋄_) ↑ (*-monoʳ g))
  *-ωcontʳ g (seq ↗ inc) = trans (trans (⊑ˣᶻ-antisym (⨆-lub′ ωCPO-⊑ˣᶻ
                                                             (λ n x → ⨆-ub n))
                                                     (⨆-lub′′ (→-DCPO (Complete-OM-Module.DCPO-⊑ (L̅-COMM Z)) X)
                                                              (λ n x → ⨆-ub n)))
                                        (*-contʳ g (seq ⇗ (λ m n →  n ⊔ᴺ m 
                                                          , (IncSeq-trans {PO = PO-⊑ˣʸ} (seq ↗ inc) m (n ⊔ᴺ m) (n≤m⊔n n m))
                                                          , (IncSeq-trans {PO = PO-⊑ˣʸ } (seq ↗ inc) n (n ⊔ᴺ m) (m≤m⊔n n m)) )) ))
                                        (cong (g ⋄_)
                                              (⊑ˣʸ-antisym (⨆-lub′′ (→-DCPO (Complete-OM-Module.DCPO-⊑ (L̅-COMM Y)) X)
                                                                    {seq ⇗ (λ m n →  n ⊔ᴺ m 
                                                                         , (IncSeq-trans {PO = PO-⊑ˣʸ} (seq ↗ inc) m (n ⊔ᴺ m) (n≤m⊔n n m))
                                                                         , (IncSeq-trans {PO = PO-⊑ˣʸ } (seq ↗ inc) n (n ⊔ᴺ m) (m≤m⊔n n m)) )}
                                                                    (λ n x → ⨆-ub n))
                                                           (⨆-lub′ ωCPO-⊑ˣʸ
                                                                   (λ n x → ⨆-ub n))))


L̅-Iteration : ElgotIteration Kl-CoC
L̅-Iteration =
  record
    { _† = λ {X} {Y} → _† {Z = Y ⊎ X}
    ; fix = λ {X} {Y} {f} → fix {Z = Y ⊎ X} f
    }
  where
    module _ {X Y Z : Set ℓ} (f : X → L̅ (Y ⊎ X)) where
      _⊑ʸ_ = _⊑_ Y
      ωCPO-⊑ʸ = DCPO→ωCPO (PO-⊑ Y) (Complete-OM-Module.DCPO-⊑ (L̅-COMM Y))
      
      PO-⊑ˣʸ = →-PO (PO-⊑ Y) X
      ωCPO-⊑ˣʸ = →-ωCPO ωCPO-⊑ʸ X
      ⨆ˣʸ = ω-CompletePartialOrder.⨆ ωCPO-⊑ˣʸ
      
      PO-⊑ʸˣʸ = →-PO (PO-⊑ Y) (Y ⊎ X)
      ωCPO-⊑ʸˣʸ = →-ωCPO ωCPO-⊑ʸ (Y ⊎ X)
      ⨆ʸˣʸ = ω-CompletePartialOrder.⨆ ωCPO-⊑ʸˣʸ

      open ω-CompletePartialOrder using (⨆-const)
      open LeastFixpoints (→-ωCPO ωCPO-⊑ʸ X)
      
      [η,]-mono : Mono PO-⊑ˣʸ PO-⊑ʸˣʸ [ η ,_]
      [η,]-mono g₁x⊑g₂x (inj₁ y) = ⊑-refl
      [η,]-mono g₁x⊑g₂x (inj₂ x) = g₁x⊑g₂x x
      [η,]-cont : ωCont ωCPO-⊑ˣʸ ωCPO-⊑ʸˣʸ ([ η ,_] ↑ [η,]-mono)
      [η,]-cont _ = →-≡ (λ { (inj₁ y) → ⨆-const ωCPO-⊑ʸ ; (inj₂ x) → refl })

      F : ContFun (→-ωCPO ωCPO-⊑ʸ X) (→-ωCPO ωCPO-⊑ʸ X)
      F = (λ g → [ η , g ] ⋄ f)
                 ↑ (λ {g₁} {g₂} g₁x⊑g₂x → *-monoˡ f ([η,]-mono g₁x⊑g₂x) ) 
                 ↝ λ { (seq ↗ inc) → trans (*-ωcontˡ f ((λ n → [ η , seq n ]) ↗ [η,]-mono ∘ inc)) 
                                           (cong (λ k → k ⋄ f) ([η,]-cont (seq ↗ inc))) } 
      _† = μ F
      fix = μ-fix F
