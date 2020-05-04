{-# OPTIONS --cubical --safe #-}

open import Level using (Level; _⊔_; Lift; lift) renaming (suc to ℓ-suc)
open import Function using (id; _∘_; _$_)
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
  This module defines the inductive-inductive data type L̅ on which the duration monad L̅ will be built. 
-
  The definition makes use of higher inductive types as in Homotopy Type Theory, 
  which is a feature of Cubical Agda. 
-}
--*

module Eliminators-L-bar {ℓ ℓ′ : Level} {M : Monoid} (OM : O-Monoid {ℓ} {ℓ′} M) where

module Def-L̅ (A : Set (ℓ ⊔ ℓ′)) where

  open O-Monoid OM renaming (PO to PO-≤)

  data L̅ : Set (ℓ ⊔ ℓ′)
  data _⊑_ : L̅ → L̅ → Set (ℓ ⊔ ℓ′)
  
  PO-⊑ : PartialOrder L̅
  _▶_ : 𝕄 → DirSeq PO-⊑ → DirSeq PO-⊑
  _▷-⊥ : DirSeq PO-≤ → DirSeq PO-⊑

  infix 4 _⊑_

  private
    variable
      a b : 𝕄
      x y z : L̅
      s : DirSeq PO-⊑
      t : DirSeq PO-≤

  data L̅ where
    _▷_ : 𝕄 → L̅ → L̅
    ⊥ : L̅
    ⨆ : (DirSeq PO-⊑) → L̅
    η : A → L̅
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
    -- ▷-contʳ⃗ follows by ⨆-lub and ▷-monoʳ (s. L̅-COMM)
    ▷⊥-cont⃖ : ∀ (⋁t : Lub PO-≤ (DirSeq.seq t)) → (Lub.ub ⋁t) ▷ ⊥ ⊑ ⨆ (t ▷-⊥)
    -- ▷⊥-cont⃗ follows by ⨆-lub and ▷⊥-mono (s. L̅-CCOMM)
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

  (seq ⇗ dir) ▷-⊥ =  -- DirSeq-mono (seq ⇗ dir) (_▷ ⊥ ↑ ▷⊥-mono) -- morally the same, module level issues
    (_▷ ⊥) ∘ seq ⇗ λ n m →
      (proj₁ $ dir n m) , (▷⊥-mono $ proj₁ $ proj₂ $ dir n m) , (▷⊥-mono $ proj₂ $ proj₂ $ dir n m)

  open PartialOrder.PartialOrder PO-⊑ using () renaming (A-set to L̅-Set)

  record Arguments {ℓ-L̅ ℓ-⊑ : Level} : Set (ℓ ⊔ ℓ′ ⊔ ℓ-suc (ℓ-L̅ ⊔ ℓ-⊑)) where
    field
      P-L̅  : L̅ → Set ℓ-L̅
      P-⊑  : P-L̅ x → P-L̅ y → x ⊑ y → Set ℓ-⊑

    P-Dir : DirSeq PO-⊑ → Set (ℓ-L̅ ⊔ ℓ-⊑)
    P-Dir s = Σ (∀ (n : ℕ) → P-L̅ (DirSeq.seq s n))
                (λ p → (∀ (n m : ℕ) → P-⊑ (p n) (p (proj₁ (DirSeq.dir s n m))) (proj₁ (proj₂ (DirSeq.dir s n m)))
                                    × P-⊑ (p m) (p (proj₁ (DirSeq.dir s n m))) (proj₂ (proj₂ (DirSeq.dir s n m)))))



    field
      P-▷ : ∀ (a : 𝕄) → P-L̅ x → P-L̅ (a ▷ x)
      P-⊥ : P-L̅ ⊥
      P-⨆ : P-Dir s → P-L̅ (⨆ s)
      P-η : ∀ (x : A) → P-L̅ (η x)
      P-⊑-antisym : ∀ {x⊑y : x ⊑ y} {y⊑x : y ⊑ x} (px : P-L̅ x) (py : P-L̅ y)
                    → P-⊑ px py x⊑y → P-⊑ py px y⊑x →
                      subst P-L̅ (⊑-antisym x⊑y y⊑x) px ≡ py
      P-⊑-refl : ∀ (p : P-L̅ x) → P-⊑ p p ⊑-refl
      P-⊑-trans : ∀ {x⊑y : x ⊑ y} {y⊑z : y ⊑ z} (px : P-L̅ x) (py : P-L̅ y) (pz : P-L̅ z) →
                    P-⊑ px py x⊑y → P-⊑ py pz y⊑z → P-⊑ px pz (⊑-trans x⊑y y⊑z)
      P-▷-sum⃗ : ∀ (px : P-L̅ x) → P-⊑ (P-▷ a (P-▷ b px)) (P-▷ (a + b) px) ▷-sum⃗
      P-▷-sum⃖ : ∀ (px : P-L̅ x) → P-⊑ (P-▷ (a + b) px) (P-▷ a (P-▷ b px)) ▷-sum⃖
      P-▷-neutrˡ⃗ : ∀ (px : P-L̅ x) → P-⊑ (P-▷ 𝟘 px) px ▷-neutrˡ⃗
      P-▷-neutrˡ⃖ : ∀ (px : P-L̅ x) → P-⊑ px (P-▷ 𝟘 px) ▷-neutrˡ⃖
      P-⊥⊑x : ∀ (p : P-L̅ x) → P-⊑ P-⊥ p ⊥⊑x
      P-▷-monoʳ : ∀ {x⊑y : x ⊑ y} (px : P-L̅ x) (py : P-L̅ y) → P-⊑ px py x⊑y → P-⊑ (P-▷ a px) (P-▷ a py) (▷-monoʳ x⊑y)
      P-▷⊥-mono : ∀ {a≤b : a ≤ b} → P-⊑ (P-▷ a P-⊥) (P-▷ b P-⊥) (▷⊥-mono a≤b)
      P-⨆-ub : ∀ (ps : P-Dir s) (n : ℕ) → P-⊑ (proj₁ ps n) (P-⨆ {s} ps) (⨆-ub n)
      P-⨆-lub : ∀ {ub : ∀ (n : ℕ) → s ⟨ n ⟩ ⊑ x} (ps : P-Dir s) (px : P-L̅ x) →
                   (∀ (n : ℕ) → P-⊑ (proj₁ ps n) px (ub n)) →
                   P-⊑ (P-⨆ {s} ps) px (⨆-lub ub)
      P-▷-contʳ⃖ : ∀ (ps : P-Dir s) → P-⊑ (P-▷ a (P-⨆ {s} ps))
                                          (P-⨆ ((λ n → P-▷ a ((proj₁ ps) n))
                                                , λ n m → (P-▷-monoʳ (proj₁ ps n) (proj₁ ps (proj₁ (DirSeq.dir s n m)))
                                                                                  (proj₁ ((proj₂ ps) n m) ))
                                                          , (P-▷-monoʳ (proj₁ ps m) (proj₁ ps (proj₁ (DirSeq.dir s n m)))
                                                                                    (proj₂ ((proj₂ ps) n m) ))))
                                          ▷-contʳ⃖   
      P-▷⊥-cont⃖ : ∀ (⋁t : Lub PO-≤ (DirSeq.seq t)) → P-⊑ (P-▷ (Lub.ub ⋁t) P-⊥)
                                                          (P-⨆ {t ▷-⊥} ((λ n → P-▷ (t ⟨ n ⟩) P-⊥)
                                                                        , λ n m → P-▷⊥-mono , P-▷⊥-mono))
                                                          (▷⊥-cont⃖ ⋁t)
      P-⊑-prop : ∀ {x⊑y : x ⊑ y} (px : P-L̅ x) (py : P-L̅ y) → IsProp (P-⊑ px py x⊑y)

  record Eliminators {ℓ-L̅ ℓ-⊑ : Level} (args : Arguments {ℓ-L̅} {ℓ-⊑}) : Set (ℓ ⊔ ℓ′ ⊔ ℓ-L̅ ⊔ ℓ-⊑)  where
    open Arguments args
  
    field
      L̅-rec : ∀ (x : L̅) → P-L̅ x
      ⊑-rec : ∀ (x⊑y : x ⊑ y) → P-⊑ (L̅-rec x) (L̅-rec y) x⊑y

    Dir-rec : ∀ (s : DirSeq PO-⊑) → P-Dir s
    Dir-rec = λ { (seq ⇗ dir) → ( (λ n → L̅-rec (seq n))
                                , (λ n m → ⊑-rec (proj₁ (proj₂ (dir n m))) ,
                                            ⊑-rec (proj₂ (proj₂ (dir n m))))  ) }
    field
      L̅-rec-▷ : L̅-rec (a ▷ x) ≡ P-▷ a (L̅-rec x)
      L̅-rec-⊥ : L̅-rec ⊥ ≡ P-⊥
      L̅-rec-⨆ : L̅-rec (⨆ s) ≡ P-⨆ (Dir-rec s)
      L̅-rec-η : ∀ {x : A} → L̅-rec (η x) ≡ P-η x

  L̅-Elim : ∀ {ℓ-L̅ ℓ-⊑ : Level} (args : Arguments {ℓ-L̅} {ℓ-⊑}) → Eliminators args
  L̅-Elim args = record
                  { L̅-rec = L̅-rec
                  ; ⊑-rec = ⊑-rec
                  ; L̅-rec-▷ = refl
                  ; L̅-rec-⊥ = refl
                  ; L̅-rec-⨆ = refl
                  ; L̅-rec-η = refl
                  }
    where
      open Arguments args
      L̅-rec : ∀ (x : L̅) → P-L̅ x
      ⊑-rec : ∀ {x y : L̅} (x⊑y : x ⊑ y) → P-⊑ (L̅-rec x) (L̅-rec y) x⊑y
      Dir-rec : (s : DirSeq PO-⊑) → P-Dir s
      
      Dir-rec = λ { (seq ⇗ dir) → ( (λ n → L̅-rec (seq n))
                                  , ((λ n m → ⊑-rec (proj₁ (proj₂ (dir n m))) ,
                                            ⊑-rec (proj₂ (proj₂ (dir n m))))  ) ) } 

      L̅-rec (a ▷ x) = P-▷ a (L̅-rec x)
      L̅-rec ⊥ = P-⊥
      L̅-rec (⨆ s) = P-⨆ (Dir-rec s)
      L̅-rec (η x) = P-η x
      L̅-rec (⊑-antisym {x} {y} x⊑y y⊑x i) = subst≡→[]≡ {P = P-L̅} (P-⊑-antisym (L̅-rec x) (L̅-rec y)
                                                                              (⊑-rec x⊑y) (⊑-rec y⊑x)) i

      ⊑-rec (⊑-refl {x}) = P-⊑-refl (L̅-rec x)
      ⊑-rec (⊑-trans {x} {y} {z} x⊑y y⊑z) = P-⊑-trans (L̅-rec x) (L̅-rec y) (L̅-rec z)
                                                      (⊑-rec x⊑y) (⊑-rec y⊑z)
      ⊑-rec (▷-sum⃗ {a} {b} {x}) = P-▷-sum⃗ (L̅-rec x)
      ⊑-rec (▷-sum⃖ {a} {b} {x}) = P-▷-sum⃖ (L̅-rec x)
      ⊑-rec (▷-neutrˡ⃗ {x}) = P-▷-neutrˡ⃗ (L̅-rec x)
      ⊑-rec (▷-neutrˡ⃖ {x}) = P-▷-neutrˡ⃖ (L̅-rec x)
      ⊑-rec (⊥⊑x {x}) = P-⊥⊑x (L̅-rec x)
      ⊑-rec (▷-monoʳ {x} {y} x⊑y) = P-▷-monoʳ (L̅-rec x) (L̅-rec y) (⊑-rec x⊑y)
      ⊑-rec (▷⊥-mono a≤b) = P-▷⊥-mono
      ⊑-rec (⨆-ub {seq ⇗ dir} n) = P-⨆-ub seq dir (Dir-rec (seq ⇗ dir)) n
      ⊑-rec (⨆-lub {seq ⇗ dir} {x} ub) = P-⨆-lub seq dir (Dir-rec (seq ⇗ dir))
                                                  (L̅-rec x) (λ n → ⊑-rec (ub n))
      ⊑-rec (▷-contʳ⃖ {a} {s}) = P-▷-contʳ⃖ (Dir-rec s)
      ⊑-rec (▷⊥-cont⃖ {seq ⇗ dir} ⋁t) = P-▷⊥-cont⃖ seq dir ⋁t
      ⊑-rec (⊑-prop {x} {y} p q i) = subst≡→[]≡ {P = P-⊑ (L̅-rec x) (L̅-rec y)} {p = ⊑-rec p} {q = ⊑-rec q}
                                                {x≡y = ⊑-prop p q} (P-⊑-prop (L̅-rec x) (L̅-rec y) _ _) i

  L̅-MM : M-Module M
  L̅-MM =
    record
      { 𝔼 = L̅
      ; _▷_ = _▷_
      ; ▷-sum = ⊑-antisym ▷-sum⃗ ▷-sum⃖
      ; ▷-neutrˡ = ⊑-antisym ▷-neutrˡ⃗ ▷-neutrˡ⃖
      }
  L̅-OMM : Ordered-M-Module {ℓ′-⊑ = ℓ ⊔ ℓ′} OM L̅-MM
  L̅-OMM = 
    record
      { ⊥ = ⊥
      ; PO-⊑ = PO-⊑
      ; ⊥⊑x = ⊥⊑x
      ; ▷-monoʳ = ▷-monoʳ
      ; ▷⊥-mono = ▷⊥-mono
      }

  L̅-COMM : Complete-OM-Module OM L̅-OMM
  L̅-COMM =
    record
      { ⨆ = ⨆
      ; ⨆-ub = ⨆-ub
      ; ⨆-lub = ⨆-lub
      ; ▷-contʳ = ⊑-antisym (⨆-lub (λ n → ▷-monoʳ (⨆-ub n)))
                            ▷-contʳ⃖
      }

  L̅-CCOMM : C-Complete-OM-Module L̅-COMM
  L̅-CCOMM = record { ▷⊥-cont = λ ⋁t → ⊑-antisym (⨆-lub (λ n → ▷⊥-mono (Lub.is-ub ⋁t n)))
                                                (▷⊥-cont⃖ ⋁t) }

  L̅-COMMo : C-Complete-OM-Module-over A OM L̅-CCOMM
  L̅-COMMo =
    record { η = η }

  private
    variable
      MM′ : M-Module M
      OMM′ : Ordered-M-Module OM MM′
      COMM′ : Complete-OM-Module OM OMM′
      CCOMM′ : C-Complete-OM-Module COMM′

  L̅-Initial : ∀ {ℓ-to ℓ-⊑-to : Level} → Initial-C-Complete-OM-Module-over ℓ-to ℓ-⊑-to L̅-COMMo
  L̅-Initial =
    record
      { H = λ CCOMMo′ → record
                         { COMMM = record
                                     { fun = h CCOMMo′
                                     ; f-⊑ = h-⊑ CCOMMo′
                                     ; f-⊥ = refl
                                     ; f-▷ = refl
                                     ; f-⨆ = refl
                                     }
                         ; f-η = refl }
      ; uniq = λ {_} {_} {_} {_} {CCOMMo′} G → →-≡ (λ x → sym (gx≡hx CCOMMo′ G x))
      }
    where
      module _ (CCOMMo′ : C-Complete-OM-Module-over A OM {COMM = COMM′} CCOMM′) where
        open C-Complete-OM-Module-over CCOMMo′ using (𝔼; 𝔼-set)
             renaming (_▷_ to _▷′_; ⊥ to ⊥′; _⊑_ to _⊑′_; ⨆ to ⨆′; η to η′
                      ; ▷-sum to ▷′-sum; ▷-neutrˡ to ▷′-neutrˡ; ⊑-antisym to ⊑′-antisym; ▷-contʳ to ▷′-contʳ; ▷⊥-cont to ▷′⊥′-cont
                      ; ⊑-refl to ⊑′-refl; ⊑-trans to ⊑′-trans; ⊥⊑x to ⊥′⊑′x; ▷-monoʳ to ▷′-monoʳ; ▷⊥-mono to ▷′⊥′-mono
                      ; ⨆-ub to ⨆′-ub; ⨆-lub to ⨆′-lub; ⊑-prop to ⊑′-prop; DirSeq-≡ to DirSeq-≡′)
        h-args : Arguments
        h-args = record
                   { P-L̅ = λ x → 𝔼
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
                   ; P-▷⊥-cont⃖ = λ seq dir ⋁t → subst (λ y → Lub.ub ⋁t ▷′ ⊥′ ⊑′ y)
                                                       (sym (▷′⊥′-cont ⋁t)) ⊑′-refl
                   ; P-⊑-prop = λ hx hy hp hq → ⊑′-prop hp hq
                   }
        h-elims : Eliminators h-args
        h-elims = L̅-Elim h-args
        open Eliminators h-elims using () renaming (L̅-rec to h; ⊑-rec to h-⊑) public
        
        module _ (G : C-Complete-OM-Module-Morphism-over L̅-COMMo CCOMMo′) where
          open Complete-OM-Module-Morphism-over G renaming (fun to g; f-⊑ to g-⊑; f-⊥ to g-⊥; f-▷ to g-▷; f-⨆ to g-⨆; f-η to g-η)
          gx≡hx-args : Arguments
          gx≡hx-args = record
                         { P-L̅ = λ x → g x ≡ h x
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
          gx≡hx-elims = L̅-Elim gx≡hx-args
          open Eliminators gx≡hx-elims using () renaming (L̅-rec to gx≡hx) public
          

open Def-L̅


L̅*-COMMo : ∀ {A B : Set (ℓ ⊔ ℓ′)} (f : A → L̅ B) → C-Complete-OM-Module-over A OM (L̅-CCOMM B)
L̅*-COMMo f = record { η = f }


