{-# OPTIONS --cubical --safe #-}

open import Level using (Level; _⊔_; Lift; lift) renaming (suc to ℓ-suc)
open import Function using (id; _∘_)
open import Data.Nat using (ℕ; suc) renaming (_≤_ to _≤ᴺ_)
open import Data.Unit using (⊤; tt)
open import Data.Empty renaming (⊥ to 𝟎)
open import Data.Product using (Σ; ∃-syntax; _×_; _,_; proj₁; proj₂)

open import CubicalIdentity using (_≡_; refl; sym; cong; cong-app; transport; trans; subst; subst2
                                  ; subst-const; →-≡; subst≡→[]≡)
open CubicalIdentity.≡-Reasoning
open import Sets

open import PartialOrder
open import Monoid 
open import MonoidModule 

--*
{-
  This module defines the inductive-inductive data type L̃ on which the duration monad L̃ will be built. 
-
  The definition makes use of higher inductive types as in Homotopy Type Theory, 
  which is a feature of Cubical Agda. 
-}
--*

module Eliminators-L-wave {ℓ ℓ′ : Level} {M : Monoid} (OM : O-Monoid {ℓ} {ℓ′} M) where

module Def-L̃ (A : Set (ℓ ⊔ ℓ′)) where

  open O-Monoid OM renaming (PO to PO-≤)

  data L̃ : Set (ℓ ⊔ ℓ′)
  data _⊑_ : L̃ → L̃ → Set (ℓ ⊔ ℓ′)
  
  PO-⊑ : PartialOrder L̃
  _▶_ : 𝕄 → DirSeq PO-⊑ → DirSeq PO-⊑

  infix 4 _⊑_

  private
    variable
      a b : 𝕄
      x y z : L̃
      s : DirSeq PO-⊑

  data L̃ where
    _▷_ : 𝕄 → L̃ → L̃
    ⊥ : L̃
    ⨆ : (DirSeq PO-⊑) → L̃
    η : A → L̃
    ⊑-antisym : x ⊑ y → y ⊑ x → x ≡ y

  data _⊑_ where
    ⊑-refl : x ⊑ x
    ⊑-trans : x ⊑ y → y ⊑ z → x ⊑ z
    ▷-sum⃗ : a ▷ (b ▷ x) ⊑ (a + b) ▷ x
    ▷-sum⃖ : (a + b) ▷ x ⊑ a ▷ (b ▷ x)
    ▷-neutrˡ⃗ : 𝟘 ▷ x ⊑ x
    ▷-neutrˡ⃖ : x ⊑ 𝟘 ▷ x
    ⊥⊑x : ⊥ ⊑ x
    ▷-monoʳ : x ⊑ y → a ▷ x ⊑ a ▷ y
    ▷⊥-mono : a ≤ b → a ▷ ⊥ ⊑ b ▷ ⊥
    ⨆-ub : ∀ (n : ℕ) → s ⟨ n ⟩ ⊑ ⨆ s
    ⨆-lub : (∀ (n : ℕ) → s ⟨ n ⟩ ⊑ x) → ⨆ s ⊑ x
    ▷-contʳ⃖ : a ▷ (⨆ s) ⊑ ⨆ (a ▶ s)
    -- ▷-contʳ⃗ follows by ⨆-lub and ▷-monoʳ (s. L̃-COMM)
    ⊑-prop : IsProp (x ⊑ y)

  PO-⊑ =
    record
      { _≤_ = _⊑_
      ; ≤-refl = ⊑-refl
      ; ≤-antisym = ⊑-antisym
      ; ≤-trans = ⊑-trans
      ; ≤-prop = ⊑-prop
      }

  a ▶ s = DirSeq-mono s (a ▷_ ↑ ▷-monoʳ)


  record Arguments {ℓ-L̃ ℓ-⊑ : Level} : Set (ℓ ⊔ ℓ′ ⊔ ℓ-suc (ℓ-L̃ ⊔ ℓ-⊑)) where
    field
      P-L̃  : L̃ → Set ℓ-L̃
      P-⊑  : P-L̃ x → P-L̃ y → x ⊑ y → Set ℓ-⊑

    P-Dir : DirSeq PO-⊑ → Set (ℓ-L̃ ⊔ ℓ-⊑)
    P-Dir s = Σ (∀ (n : ℕ) → P-L̃ (DirSeq.seq s n))
                (λ p → (∀ (n m : ℕ) → P-⊑ (p n) (p (proj₁ (DirSeq.dir s n m))) (proj₁ (proj₂ (DirSeq.dir s n m)))
                                    × P-⊑ (p m) (p (proj₁ (DirSeq.dir s n m))) (proj₂ (proj₂ (DirSeq.dir s n m)))))



    field
      P-▷ : ∀ (a : 𝕄) → P-L̃ x → P-L̃ (a ▷ x)
      P-⊥ : P-L̃ ⊥
      P-⨆ : P-Dir s → P-L̃ (⨆ s)
      P-η : ∀ (x : A) → P-L̃ (η x)
      P-⊑-antisym : ∀ {x⊑y : x ⊑ y} {y⊑x : y ⊑ x} (px : P-L̃ x) (py : P-L̃ y)
                    → P-⊑ px py x⊑y → P-⊑ py px y⊑x →
                      subst P-L̃ (⊑-antisym x⊑y y⊑x) px ≡ py
      P-⊑-refl : ∀ (p : P-L̃ x) → P-⊑ p p ⊑-refl
      P-⊑-trans : ∀ {x⊑y : x ⊑ y} {y⊑z : y ⊑ z} (px : P-L̃ x) (py : P-L̃ y) (pz : P-L̃ z) →
                    P-⊑ px py x⊑y → P-⊑ py pz y⊑z → P-⊑ px pz (⊑-trans x⊑y y⊑z)
      P-▷-sum⃗ : ∀ (px : P-L̃ x) → P-⊑ (P-▷ a (P-▷ b px)) (P-▷ (a + b) px) ▷-sum⃗
      P-▷-sum⃖ : ∀ (px : P-L̃ x) → P-⊑ (P-▷ (a + b) px) (P-▷ a (P-▷ b px)) ▷-sum⃖
      P-▷-neutrˡ⃗ : ∀ (px : P-L̃ x) → P-⊑ (P-▷ 𝟘 px) px ▷-neutrˡ⃗
      P-▷-neutrˡ⃖ : ∀ (px : P-L̃ x) → P-⊑ px (P-▷ 𝟘 px) ▷-neutrˡ⃖
      P-⊥⊑x : ∀ (p : P-L̃ x) → P-⊑ P-⊥ p ⊥⊑x
      P-▷-monoʳ : ∀ {x⊑y : x ⊑ y} (px : P-L̃ x) (py : P-L̃ y) → P-⊑ px py x⊑y → P-⊑ (P-▷ a px) (P-▷ a py) (▷-monoʳ x⊑y)
      P-▷⊥-mono : ∀ {a≤b : a ≤ b} → P-⊑ (P-▷ a P-⊥) (P-▷ b P-⊥) (▷⊥-mono a≤b)
      P-⨆-ub : ∀ (ps : P-Dir s) (n : ℕ) → P-⊑ (proj₁ ps n) (P-⨆ {s} ps) (⨆-ub n)
      P-⨆-lub : ∀ {ub : ∀ (n : ℕ) → s ⟨ n ⟩ ⊑ x} (ps : P-Dir s) (px : P-L̃ x) →
                   (∀ (n : ℕ) → P-⊑ (proj₁ ps n) px (ub n)) →
                   P-⊑ (P-⨆ {s} ps) px (⨆-lub ub)
      P-▷-contʳ⃖ : ∀ (ps : P-Dir s) → P-⊑ (P-▷ a (P-⨆ {s} ps))
                                          (P-⨆ ((λ n → P-▷ a ((proj₁ ps) n))
                                                , λ n m → (P-▷-monoʳ (proj₁ ps n) (proj₁ ps (proj₁ (DirSeq.dir s n m)))
                                                                                  (proj₁ ((proj₂ ps) n m) ))
                                                        , (P-▷-monoʳ (proj₁ ps m) (proj₁ ps (proj₁ (DirSeq.dir s n m)))
                                                                                  (proj₂ ((proj₂ ps) n m) ))))
                                          ▷-contʳ⃖   

      P-⊑-prop : ∀ {x⊑y : x ⊑ y} (px : P-L̃ x) (py : P-L̃ y) → IsProp (P-⊑ px py x⊑y)


  record Eliminators {ℓ-L̃ ℓ-⊑ : Level} (args : Arguments {ℓ-L̃} {ℓ-⊑}) : Set (ℓ ⊔ ℓ′ ⊔ ℓ-L̃ ⊔ ℓ-⊑) where
    open Arguments args
  
    field
      L̃-rec : ∀ (x : L̃) → P-L̃ x
      ⊑-rec : ∀ (x⊑y : x ⊑ y) → P-⊑ (L̃-rec x) (L̃-rec y) x⊑y

    Dir-rec : ∀ (s : DirSeq PO-⊑) → P-Dir s
    Dir-rec = λ { (seq ⇗ dir) → ( (λ n → L̃-rec (seq n))
                                , (λ n m → ⊑-rec (proj₁ (proj₂ (dir n m))) ,
                                            ⊑-rec (proj₂ (proj₂ (dir n m))))  ) }
    field
      L̃-rec-▷ : L̃-rec (a ▷ x) ≡ P-▷ a (L̃-rec x)
      L̃-rec-⊥ : L̃-rec ⊥ ≡ P-⊥
      L̃-rec-⨆ : L̃-rec (⨆ s) ≡ P-⨆ (Dir-rec s)
      L̃-rec-η : ∀ {x : A} → L̃-rec (η x) ≡ P-η x

  L̃-Elim : ∀ {ℓ-L̃ ℓ-⊑ : Level} (args : Arguments {ℓ-L̃} {ℓ-⊑}) → Eliminators args
  L̃-Elim args = record
                  { L̃-rec = L̃-rec
                  ; ⊑-rec = ⊑-rec
                  ; L̃-rec-▷ = refl
                  ; L̃-rec-⊥ = refl
                  ; L̃-rec-⨆ = refl
                  ; L̃-rec-η = refl
                  }
    where
      open Arguments args
      L̃-rec : ∀ (x : L̃) → P-L̃ x
      ⊑-rec : ∀ {x y : L̃} (x⊑y : x ⊑ y) → P-⊑ (L̃-rec x) (L̃-rec y) x⊑y
      Dir-rec : (s : DirSeq PO-⊑) → P-Dir s
      
      Dir-rec = λ { (seq ⇗ dir) → ( (λ n → L̃-rec (seq n))
                                  , ((λ n m → ⊑-rec (proj₁ (proj₂ (dir n m))) ,
                                            ⊑-rec (proj₂ (proj₂ (dir n m))))  ) ) } 

      L̃-rec (a ▷ x) = P-▷ a (L̃-rec x)
      L̃-rec ⊥ = P-⊥
      L̃-rec (⨆ s) = P-⨆ (Dir-rec s)
      L̃-rec (η x) = P-η x
      L̃-rec (⊑-antisym {x} {y} x⊑y y⊑x i) = subst≡→[]≡ {P = P-L̃} (P-⊑-antisym (L̃-rec x) (L̃-rec y)
                                                                              (⊑-rec x⊑y) (⊑-rec y⊑x)) i

      ⊑-rec (⊑-refl {x}) = P-⊑-refl (L̃-rec x)
      ⊑-rec (⊑-trans {x} {y} {z} x⊑y y⊑z) = P-⊑-trans (L̃-rec x) (L̃-rec y) (L̃-rec z)
                                                      (⊑-rec x⊑y) (⊑-rec y⊑z)
      ⊑-rec (▷-sum⃗ {a} {b} {x}) = P-▷-sum⃗ (L̃-rec x)
      ⊑-rec (▷-sum⃖ {a} {b} {x}) = P-▷-sum⃖ (L̃-rec x)
      ⊑-rec (▷-neutrˡ⃗ {x}) = P-▷-neutrˡ⃗ (L̃-rec x)
      ⊑-rec (▷-neutrˡ⃖ {x}) = P-▷-neutrˡ⃖ (L̃-rec x)
      ⊑-rec (⊥⊑x {x}) = P-⊥⊑x (L̃-rec x)
      ⊑-rec (▷-monoʳ {x} {y} x⊑y) = P-▷-monoʳ (L̃-rec x) (L̃-rec y) (⊑-rec x⊑y)
      ⊑-rec (▷⊥-mono a≤b) = P-▷⊥-mono
      ⊑-rec (⨆-ub {seq ⇗ Dir} n) = P-⨆-ub seq Dir (Dir-rec (seq ⇗ Dir)) n
      ⊑-rec (⨆-lub {seq ⇗ Dir} {x} ub) = P-⨆-lub seq Dir (Dir-rec (seq ⇗ Dir))
                                                  (L̃-rec x) (λ n → ⊑-rec (ub n))
      ⊑-rec (▷-contʳ⃖ {a} {s}) = P-▷-contʳ⃖ (Dir-rec s)
      ⊑-rec (⊑-prop {x} {y} p q i) = subst≡→[]≡ {P = P-⊑ (L̃-rec x) (L̃-rec y)} {p = ⊑-rec p} {q = ⊑-rec q}
                                                {x≡y = ⊑-prop p q} (P-⊑-prop (L̃-rec x) (L̃-rec y) _ _) i

  L̃-MM : M-Module M
  L̃-MM =
    record
      { 𝔼 = L̃
      ; _▷_ = _▷_
      ; ▷-sum = ⊑-antisym ▷-sum⃗ ▷-sum⃖
      ; ▷-neutrˡ = ⊑-antisym ▷-neutrˡ⃗ ▷-neutrˡ⃖
      }
  L̃-OMM : Ordered-M-Module {ℓ′-⊑ = ℓ ⊔ ℓ′} OM L̃-MM
  L̃-OMM = 
    record
      { ⊥ = ⊥
      ; PO-⊑ = PO-⊑
      ; ⊥⊑x = ⊥⊑x
      ; ▷-monoʳ = ▷-monoʳ
      ; ▷⊥-mono = ▷⊥-mono
      }


  L̃-COMM : Complete-OM-Module OM L̃-OMM
  L̃-COMM =
    record
      { ⨆ = ⨆
      ; ⨆-ub = ⨆-ub
      ; ⨆-lub = ⨆-lub
      ; ▷-contʳ = ⊑-antisym (⨆-lub (λ n → ▷-monoʳ (⨆-ub n))) ▷-contʳ⃖
      }

  L̃-COMMo : Complete-OM-Module-over A OM L̃-COMM
  L̃-COMMo =
    record { η = η }

  private
    variable
      MM′ : M-Module M
      OMM′ : Ordered-M-Module OM MM′
      COMM′ : Complete-OM-Module OM OMM′
                                    
  L̃-Initial : ∀ {ℓ-to ℓ-⊑-to : Level} → Initial-Complete-OM-Module-over ℓ-to ℓ-⊑-to L̃-COMMo
  L̃-Initial =
    record
      { H = λ COMMo′ → record
                         { COMMM = record
                                     { fun = h COMMo′
                                     ; f-⊑ = h-⊑ COMMo′
                                     ; f-⊥ = refl
                                     ; f-▷ = refl
                                     ; f-⨆ = refl
                                     }
                         ; f-η = refl }
      ; uniq = λ {_} {_} {_} {COMMo′} G → →-≡ (λ x → sym (gx≡hx COMMo′ G x))
      }
    where
      module _ (COMMo′ : Complete-OM-Module-over A OM COMM′) where
        open Complete-OM-Module-over COMMo′ using (𝔼; 𝔼-set)
             renaming (_▷_ to _▷′_; ⊥ to ⊥′; _⊑_ to _⊑′_; ⨆ to ⨆′; η to η′
                      ; ▷-sum to ▷′-sum; ▷-neutrˡ to ▷′-neutrˡ; ⊑-antisym to ⊑′-antisym; ▷-contʳ to ▷′-contʳ
                      ; ⊑-refl to ⊑′-refl; ⊑-trans to ⊑′-trans; ⊥⊑x to ⊥′⊑′x; ▷-monoʳ to ▷′-monoʳ; ▷⊥-mono to ▷′⊥′-mono
                      ; ⨆-ub to ⨆′-ub; ⨆-lub to ⨆′-lub; ⊑-prop to ⊑′-prop; DirSeq-≡ to DirSeq-≡′)
        h-args : Arguments
        h-args = record
                   { P-L̃ = λ x → 𝔼
                   ; P-⊑ = λ hx hy p → hx ⊑′ hy
                   ; P-▷ = λ a hx → a ▷′ hx
                   ; P-⊥ = ⊥′
                   ; P-⨆ = λ { {seq ⇗ dir} (h-seq , h-dir) → ⨆′ (h-seq ⇗ λ n m → (proj₁ (dir n m)) , h-dir n m)} 
                   ; P-η = λ x → η′ x
                   ; P-⊑-antisym = λ {x} {y} {x⊑y} {y⊑x} hx hy hx⊑′hy hy⊑′hx
                                   → trans (subst-const (⊑-antisym x⊑y y⊑x)) (⊑′-antisym hx⊑′hy hy⊑′hx)
                   ; P-⊑-refl = λ hx → ⊑′-refl
                   ; P-⊑-trans = λ hx hy hz hx⊑′hy hy⊑′hz → ⊑′-trans hx⊑′hy hy⊑′hz
                   ; P-▷-sum⃗ = λ {_} {a} {b} hx → subst (λ y → a ▷′ (b ▷′ hx) ⊑′ y) ▷′-sum ⊑′-refl
                   ; P-▷-sum⃖ = λ {_} {a} {b} hx → subst (λ y → y ⊑′ a ▷′ (b ▷′ hx)) ▷′-sum ⊑′-refl
                   ; P-▷-neutrˡ⃗ = λ hx → subst (λ y → 𝟘 ▷′ hx ⊑′ y) ▷′-neutrˡ ⊑′-refl
                   ; P-▷-neutrˡ⃖ = λ hx → subst (λ y → y ⊑′ 𝟘 ▷′ hx) ▷′-neutrˡ ⊑′-refl
                   ; P-⊥⊑x = λ hx → ⊥′⊑′x
                   ; P-▷-monoʳ = λ hx hy hx⊑′hy → ▷′-monoʳ hx⊑′hy
                   ; P-▷⊥-mono = λ {a} {b} {a≤b} → ▷′⊥′-mono a≤b
                   ; P-⨆-ub = λ seq Dir hs n → ⨆′-ub n
                   ; P-⨆-lub = λ seq Dir hs hx h-ub → ⨆′-lub h-ub
                   ; P-▷-contʳ⃖ = λ { {seq ⇗ dir} {a} (h-seq , h-dir)
                                  → subst (λ y → a ▷′ ⨆′ (h-seq ⇗ (λ n m → proj₁ (dir n m) , h-dir n m)) ⊑′ y)
                                          (sym ▷′-contʳ) ⊑′-refl }
                   ; P-⊑-prop = λ hx hy hp hq → ⊑′-prop hp hq
                   }
        h-elims : Eliminators h-args
        h-elims = L̃-Elim h-args
        open Eliminators h-elims using () renaming (L̃-rec to h; ⊑-rec to h-⊑) public
        
        module _ (G : Complete-OM-Module-Morphism-over L̃-COMMo COMMo′) where
          open Complete-OM-Module-Morphism-over G renaming (fun to g; f-⊑ to g-⊑; f-⊥ to g-⊥; f-▷ to g-▷; f-⨆ to g-⨆; f-η to g-η)
          gx≡hx-args : Arguments
          gx≡hx-args = record
                         { P-L̃ = λ x → g x ≡ h x
                         ; P-⊑ = λ _ _ _ → ⊤
                         ; P-▷ = λ a gx≡hx → trans g-▷ (cong (a ▷′_) gx≡hx)
                         ; P-⊥ = g-⊥
                         ; P-⨆ = λ { (p-seq , p-Dir) → trans g-⨆ (DirSeq-≡′ (→-≡ (λ n → p-seq n))) } 
                         ; P-η = λ x → cong-app g-η x
                         ; P-⊑-antisym = λ gx≡hx gy≡hy _ _ → 𝔼-set _ _
                         -- the missing cases for P-⊑ can be inferred by the type checker
                         ; P-⊑-prop = λ { _ _ tt tt → refl }
                         }
          gx≡hx-elims : Eliminators gx≡hx-args
          gx≡hx-elims = L̃-Elim gx≡hx-args
          open Eliminators gx≡hx-elims using () renaming (L̃-rec to gx≡hx) public
          

open Def-L̃

L̃*-COMMo : ∀ {A B : Set (ℓ ⊔ ℓ′)} (f : A → L̃ B) → Complete-OM-Module-over A OM (L̃-COMM B)
L̃*-COMMo f = record { η = f }
