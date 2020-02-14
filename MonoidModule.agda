{-# OPTIONS --cubical --safe #-}

open import Level using (Level; _⊔_) renaming (suc to ℓ-suc)
open import Function using (id; _∘_; _$_)
open import Data.Nat using (ℕ)
open import Data.Product using (Σ; proj₁; proj₂; _,_)

open import CubicalIdentity using (_≡_; refl; sym; cong; trans; subst)

open import PartialOrder
open import CompletePartialOrder
open import Monoid

open import Category

--*
{-
  This module introduces the notion of monoid 𝕄-module, ordered 𝕄-module, 
  (directed) complete 𝕄-module and conservative complete 𝕄-module. 
-}
--*

module MonoidModule where

private
  variable
    ℓ ℓ′ ℓ-⊑ ℓ′-⊑ : Level

record M-Module (M : Monoid {ℓ}) : Set (ℓ ⊔ (ℓ-suc ℓ′)) where
  open Monoid.Monoid M

  infix 6 _▷_
  
  field
    𝔼 : Set ℓ′
    _▷_ : 𝕄 → 𝔼 → 𝔼
    ▷-sum : ∀ {a b : 𝕄} {x : 𝔼} → a ▷ (b ▷ x) ≡ (a + b) ▷ x 
    ▷-neutrˡ : ∀ {x : 𝔼} → 𝟘 ▷ x ≡ x

private
  variable
    M : Monoid
    OM : O-Monoid M
    MM MM′ : M-Module M  

record Ordered-M-Module (OM : O-Monoid {ℓ} {ℓ-⊑} M) (MM : M-Module {ℓ} {ℓ′} M) : Set (ℓ ⊔ ℓ-⊑ ⊔ (ℓ-suc (ℓ′-⊑ ⊔ ℓ′))) where
  open O-Monoid OM renaming (PO to PO-≤)
  open M-Module MM public

  field
    ⊥ : 𝔼
    PO-⊑ : PartialOrder {ℓ′} {ℓ′-⊑} 𝔼

  open PartialOrder.PartialOrder PO-⊑
    renaming (_≤_ to _⊑_; ≤-refl to ⊑-refl; ≤-antisym to ⊑-antisym; ≤-trans to ⊑-trans
             ; ≤-prop to ⊑-prop; A-set to 𝔼-set) public

  field
    ⊥⊑x : ∀ {x : 𝔼} → ⊥ ⊑ x
    ▷-monoʳ : ∀ {a : 𝕄} {x y : 𝔼} → x ⊑ y → a ▷ x ⊑ a ▷ y
    ▷⊥-mono : ∀ {a b : 𝕄} → a ≤ b → a ▷ ⊥ ⊑ b ▷ ⊥

module _ (OM : O-Monoid {ℓ} {ℓ-⊑} M) (OMM : Ordered-M-Module {ℓ′ = ℓ′} {ℓ′-⊑} OM MM) where

  private
    variable
      s : DirSeq (Ordered-M-Module.PO-⊑ OMM)

  record Complete-OM-Module : Set (ℓ ⊔ ℓ-⊑ ⊔ ℓ′ ⊔ ℓ′-⊑) where
    open O-Monoid OM renaming (PO to PO-≤)
    open Ordered-M-Module OMM public
    
    field
      ⨆ : DirSeq PO-⊑ → 𝔼
      ⨆-ub : ∀ (n : ℕ) → s ⟨ n ⟩ ⊑ ⨆ s
      ⨆-lub : ∀ {b : 𝔼} → (∀ (n : ℕ) → s ⟨ n ⟩ ⊑ b) → ⨆ s ⊑ b

    _▶_ : 𝕄 → DirSeq PO-⊑ → DirSeq PO-⊑
    _▶_ = λ { a (seq ⇗ dir) →
            ((a ▷_) ∘ seq) ⇗ λ n m →
              (proj₁ $ dir n m) ,
              ▷-monoʳ (proj₁ $ proj₂ $ dir n m) ,
              ▷-monoʳ (proj₂ $ proj₂ $ dir n m) }
    
    field
      ▷-contʳ : ∀ {a : 𝕄} → ⨆ (a ▶ s) ≡ a ▷ ⨆ s

    DCPO-⊑ : D-CompletePartialOrder PO-⊑
    DCPO-⊑ = record
              { ⊥ = ⊥
              ; ⊥⊑x = ⊥⊑x
              ; ⨆ = ⨆
              ; ⨆-ub = ⨆-ub
              ; ⨆-lub = ⨆-lub
              }

    DirSeq-≡ : ∀ {s t : ℕ → 𝔼} {dirₛ : Dir PO-⊑ s} {dirₜ : Dir PO-⊑ t}
               → (s ≡ t) → ⨆ (s ⇗ dirₛ) ≡ ⨆ (t ⇗ dirₜ)
    DirSeq-≡ {s} {t} s≡t =
      ⊑-antisym (⨆-lub $ λ n → ⊑-trans (subst (λ u → s n ⊑ u n) s≡t ⊑-refl) (⨆-ub n))
                (⨆-lub $ λ n → ⊑-trans (subst (λ u → t n ⊑ u n) (sym s≡t) ⊑-refl) (⨆-ub n)) 


private
  variable
    ℓ₁ ℓ₂ ℓ₁-⊑ ℓ₂-⊑ : Level
    OMM OMM₁ OMM₂ OMM₃ OMM′ : Ordered-M-Module OM MM
    COMM COMM₁ COMM₂ COMM₃ COMM′ : Complete-OM-Module OM OMM

-- Conservative complete M-module
record C-Complete-OM-Module (COMM : Complete-OM-Module {ℓ} {ℓ-⊑} {M} {ℓ} {ℓ-⊑} OM OMM) : Set (ℓ ⊔ ℓ-⊑) where
  open O-Monoid OM renaming (PO to PO-≤)
  open Complete-OM-Module COMM public

  _▷-⊥ : DirSeq PO-≤ → DirSeq PO-⊑
  _▷-⊥ = λ a → DirSeq-mono a ((_▷ ⊥) ↑ ▷⊥-mono)

  field
    ▷⊥-cont : ∀ {a : DirSeq PO-≤} (⋁a : Lub PO-≤ (DirSeq.seq a)) → ⨆ (a ▷-⊥) ≡ (Lub.ub ⋁a) ▷ ⊥
    

record Complete-OM-Module-Morphism (COMM₁ : Complete-OM-Module {ℓ} {ℓ-⊑} {M} {ℓ₁} {ℓ₁-⊑} OM OMM₁)
         (COMM₂ : Complete-OM-Module {ℓ} {ℓ-⊑} {M} {ℓ₂} {ℓ₂-⊑} OM OMM₂) : Set (ℓ ⊔ ℓ-⊑ ⊔ ℓ₁ ⊔ ℓ₁-⊑ ⊔ ℓ₂ ⊔ ℓ₂-⊑) where
  open O-Monoid OM
  open Complete-OM-Module COMM₁ using (𝔼; 𝔼-set) renaming (_⊑_ to _⊑₁_; ⊥ to ⊥₁; _▷_ to _▷₁_; ⨆ to ⨆₁; PO-⊑ to PO-⊑₁
                                                          ; ▷-neutrˡ to ▷₁-neutrˡ)
  open Complete-OM-Module COMM₂ using () renaming (𝔼 to 𝔽; _⊑_ to _⊑₂_; ⊥ to ⊥₂; _▷_ to _▷₂_; ⨆ to ⨆₂; 𝔼-set to 𝔽-set; PO-⊑ to PO-⊑₂
                                                  ; ▷-neutrˡ to ▷₂-neutrˡ)

  field
    fun : 𝔼 → 𝔽
    f-⊑ : ∀ {x y : 𝔼} → x ⊑₁ y → fun x ⊑₂ fun y
    f-⊥ : fun ⊥₁ ≡ ⊥₂
    f-▷ : ∀ {a : 𝕄} {x : 𝔼} → fun (a ▷₁ x) ≡ a ▷₂ (fun x)
  
  fun-∘_ : DirSeq PO-⊑₁ → DirSeq PO-⊑₂
  fun-∘_ = λ { (seq ⇗ dir) →
                    fun ∘ seq ⇗ λ n m →
                        (proj₁ $ dir n m) ,
                        (f-⊑ $ proj₁ $ proj₂ $ dir n m) ,
                        (f-⊑ $ proj₂ $ proj₂ $ dir n m)  }

  field
    f-⨆ : ∀ {s : DirSeq PO-⊑₁} → fun (⨆₁ s) ≡ ⨆₂ (fun-∘ s)

C-Complete-OM-Module-Morphism : (C-Complete-OM-Module {ℓ} {ℓ-⊑} {OM = OM} COMM₁) →
                                (C-Complete-OM-Module {ℓ} {ℓ-⊑} {OM = OM} COMM₂) → Set (ℓ ⊔ ℓ-⊑)
C-Complete-OM-Module-Morphism {COMM₁ = COMM₁} {COMM₂ = COMM₂} CCOMM₁ CCOMM₂ =
  Complete-OM-Module-Morphism COMM₁ COMM₂


COMMM-id : Complete-OM-Module-Morphism COMM COMM
COMMM-id =
  record
    { fun = id
    ; f-⊑ = id
    ; f-⊥ = refl
    ; f-▷ = refl
    ; f-⨆ = refl
    }

_COMMM-∘_ : Complete-OM-Module-Morphism COMM₂ COMM₃ → Complete-OM-Module-Morphism COMM₁ COMM₂ →
            Complete-OM-Module-Morphism COMM₁ COMM₃
G COMMM-∘ F =
  record
    { fun = g ∘ f
    ; f-⊑ = g-⊑ ∘ f-⊑
    ; f-⊥ = trans (cong g f-⊥) g-⊥
    ; f-▷ = trans (cong g f-▷) g-▷
    ; f-⨆ = trans (cong g f-⨆) g-⨆
    }
  where
    open Complete-OM-Module-Morphism F renaming (fun to f)
    open Complete-OM-Module-Morphism G renaming (fun to g; f-⊑ to g-⊑; f-⊥ to g-⊥; f-▷ to g-▷; f-⨆ to g-⨆)

module _ {ℓ-A : Level} (A : Set ℓ-A) (OM : O-Monoid {ℓ} {ℓ-⊑} M) where

  record Complete-OM-Module-over (COMM : Complete-OM-Module {ℓ′ = ℓ′} {ℓ′-⊑} OM OMM) : Set (ℓ ⊔ ℓ-⊑ ⊔ ℓ′ ⊔ ℓ′-⊑ ⊔ ℓ-A) where
    open Complete-OM-Module COMM public
  
    field
      η : A → 𝔼

  record C-Complete-OM-Module-over (CCOMM : C-Complete-OM-Module {ℓ} {ℓ-⊑} {OM = OM} COMM) : Set (ℓ ⊔ ℓ-⊑ ⊔ ℓ-A) where
    open C-Complete-OM-Module CCOMM public
  
    field
      η : A → 𝔼

    COMMo : Complete-OM-Module-over COMM
    COMMo = record { η = η }


module _ {ℓ-A : Level} {A : Set ℓ-A} {OM : O-Monoid {ℓ} {ℓ-⊑} M} where
  
  record Complete-OM-Module-Morphism-over (COMMo₁ : Complete-OM-Module-over A OM {ℓ₁} {ℓ₁-⊑} COMM₁)
                                          (COMMo₂ : Complete-OM-Module-over A OM {ℓ₂} {ℓ₂-⊑} COMM₂)
                                          : Set (ℓ ⊔ ℓ-⊑ ⊔ ℓ₁ ⊔ ℓ₁-⊑ ⊔ ℓ₂ ⊔ ℓ₂-⊑ ⊔ ℓ-A) where
    open Complete-OM-Module-over COMMo₁ renaming (η to η₁)
    open Complete-OM-Module-over COMMo₂ renaming (η to η₂)
    
    field
      COMMM : Complete-OM-Module-Morphism COMM₁ COMM₂
                                                        
    open Complete-OM-Module-Morphism COMMM public
                                                   
    field
      f-η : fun ∘ η₁ ≡ η₂

  private
    variable
      COMMo′ COMMo₁ COMMo₂ COMMo₃ : Complete-OM-Module-over A OM COMM

  COMMMo-id : Complete-OM-Module-Morphism-over COMMo′ COMMo′
  COMMMo-id =
    record
      { COMMM = COMMM-id
      ; f-η = refl
      }

  _COMMMo-∘_ : Complete-OM-Module-Morphism-over COMMo₂ COMMo₃ → Complete-OM-Module-Morphism-over COMMo₁ COMMo₂ →
               Complete-OM-Module-Morphism-over COMMo₁ COMMo₃
  G COMMMo-∘ F =
    record
      { COMMM = COMMM₂₃ COMMM-∘ COMMM₁₂
      ; f-η = trans (cong (g ∘_) f-η) g-η
      }
    where
      open Complete-OM-Module-Morphism-over F renaming (COMMM to COMMM₁₂; fun to f)
      open Complete-OM-Module-Morphism-over G renaming (COMMM to COMMM₂₃; fun to g; f-η to g-η)

  record Initial-Complete-OM-Module-over (ℓ-to ℓ-⊑-to : Level)
                                         (COMMo : Complete-OM-Module-over A OM {ℓ′} {ℓ′-⊑} COMM)
                                         : Set (ℓ ⊔ ℓ-⊑ ⊔ ℓ′ ⊔ ℓ′-⊑ ⊔ (ℓ-suc (ℓ-to ⊔ ℓ-⊑-to)) ⊔ ℓ-A) where
    open Complete-OM-Module-over COMMo public
    open Complete-OM-Module-Morphism-over
    
    field
      H : ∀ (COMMo′ : Complete-OM-Module-over A OM {ℓ-to} {ℓ-⊑-to} COMM′) → Complete-OM-Module-Morphism-over COMMo COMMo′
      uniq : ∀ {COMM′ : Complete-OM-Module {MM = MM′} OM OMM′}
               {COMMo′ : Complete-OM-Module-over A OM COMM′}
               (G : Complete-OM-Module-Morphism-over COMMo COMMo′)
             → fun (H COMMo′) ≡ fun G

  private
    variable
      CCOMM CCOMM₁ CCOMM₂ CCOMM′ : C-Complete-OM-Module COMM

  C-Complete-OM-Module-Morphism-over : (C-Complete-OM-Module-over {ℓ} {ℓ-⊑} A OM CCOMM₁) →
                                       (C-Complete-OM-Module-over {ℓ} {ℓ-⊑} A OM CCOMM₂) → Set (ℓ ⊔ ℓ-⊑ ⊔ ℓ-A)
  C-Complete-OM-Module-Morphism-over CCOMMo₁ CCOMMo₂ =
    Complete-OM-Module-Morphism-over (COMMo CCOMMo₁) (COMMo CCOMMo₂)
      where
        open C-Complete-OM-Module-over

  record Initial-C-Complete-OM-Module-over (CCOMMo : C-Complete-OM-Module-over {ℓ} {ℓ-⊑} A OM CCOMM)
                                           : Set (ℓ-suc (ℓ ⊔ ℓ-⊑) ⊔ ℓ-A) where
    open C-Complete-OM-Module-over CCOMMo public
    open Complete-OM-Module-Morphism-over
      
    field
      H : ∀ (CCOMMo′ : C-Complete-OM-Module-over A OM CCOMM′) → C-Complete-OM-Module-Morphism-over CCOMMo CCOMMo′
      uniq : ∀ {COMM′ : Complete-OM-Module {MM = MM′} OM OMM′}
               {CCOMM′ : C-Complete-OM-Module COMM′}
               {CCOMMo′ : C-Complete-OM-Module-over A OM CCOMM′}
               (G : C-Complete-OM-Module-Morphism-over CCOMMo CCOMMo′)
             → fun (H CCOMMo′) ≡ fun G
