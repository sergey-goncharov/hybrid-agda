{-# OPTIONS --cubical --safe #-}

open import Level using (Level; _⊔_) renaming (suc to ℓ-suc)
open import Function using (id; _∘_; _$_)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥-elim)
open import Data.Nat using (ℕ; zero; suc)
                     renaming (_⊔_ to _⊔ᴺ_; _+_ to _+ᴺ_; _≤_ to _≤ᴺ_; z≤n to z≤ᴺn; s≤s to s≤ᴺs; ≤-pred to ≤ᴺ-pred)
open import Data.Nat.Properties using (m≤m⊔n; n≤m⊔n; +-suc; +-identityʳ; _≤?_)
open import Data.Product using (Σ; ∃-syntax; _×_; _,_; proj₁; proj₂)
open import Relation.Nullary
open import Relation.Nullary.Product
open import Relation.Nullary.Negation
open import Data.Sum as Sum using (_⊎_; inj₁; inj₂; [_,_])
import Data.Empty

open import CubicalIdentity using (_≡_; refl; sym; trans; cong; subst; subst2; →-≡; builtin-to-≡)
open CubicalIdentity.≡-Reasoning
open import Sets

open import PartialOrder

--*
{-
  
  This module introduces three notions of completeness for partial orders:

  (a) chain completeness
  (b) intensional directed completeness
  (c) extensional directed completeness

  These are related as follows: 
  
  (c) -> (b) (‖DCPO‖→DCPO below)
  (b) -> (a) (DCPO→ωCPO below)
  (a) -> (c) under decidability of the carrier (see module DecidableOrder)
  (b) -> (c) under countable choice (DCPO→‖DCPO‖ below)

  For (a), (b) and (c) there are three corresponding notions of continuity 
  below and a formalization of Kleene fixpoint theorem based on (a)

-}
--*

module CompletePartialOrder where

private
  variable
    ℓ ℓ′ : Level
    A B : Set ℓ

module _ (PO : PartialOrder {ℓ} {ℓ′} A) where

  private
    variable
      s   : IncSeq PO
      t   : DirSeq PO
      ‖t‖ : ‖DirSeq‖ PO
      
  -- ω-Complete (Pointed) Partial Order
  record ω-CompletePartialOrder : Set (ℓ ⊔ ℓ′) where

    open PartialOrder.PartialOrder PO
      renaming (_≤_ to _⊑_; ≤-refl to ⊑-refl; ≤-antisym to ⊑-antisym
        ; ≤-trans to ⊑-trans; ≤-prop to ⊑-prop; A-set to 𝔼-set) public

    field
      ⊥ : A
      ⊥⊑x : ∀ {x : A} → ⊥ ⊑ x
      ⨆ : IncSeq PO → A
      ⨆-ub : ∀ (n : ℕ) → s [ n ] ⊑ ⨆ s
      ⨆-lub : ∀ {b : A} → (∀ (n : ℕ) → s [ n ] ⊑ b) → ⨆ s ⊑ b

    ⨆-const : ∀ {x : A} {inc : Inc PO (λ _ → x)} → ⨆ ((λ _ → x) ↗ inc) ≡ x
    ⨆-const {x} {inc} = ⊑-antisym (⨆-lub (λ n → ⊑-refl)) (⨆-ub {s = (λ _ → x) ↗ inc } 0)
    
    ⨆-eq : ∀ {s t : Seq PO} {p : Inc PO s} {q : Inc PO t} → s ≡ t → ⨆ (s ↗ p) ≡ ⨆ (t ↗ q)
    ⨆-eq s≡t = cong ⨆ (IncSeq-≡ s≡t)

    Cofinal→⨆-⊑ : ∀ {s t : Seq PO} {p : Inc PO s} {q : Inc PO t} → Cofinal PO s t → ⨆ (s ↗ p) ⊑ ⨆ (t ↗ q)
    Cofinal→⨆-⊑ {s} {t} {p} {q} cof = cofinal-lubs PO s t cof 
      record
        { ub    = ⨆ (s ↗ p)
        ; is-ub = ⨆-ub 
        ; is-l  = ⨆-lub
        } 
      record
        { ub    = ⨆ (t ↗ q)
        ; is-ub = ⨆-ub 
        ; is-l  = ⨆-lub
        } 

    Cofinal→⨆-≡ : ∀ {s t : Seq PO} {p : Inc PO s} {q : Inc PO t} → Cofinal PO s t → Cofinal PO t s → ⨆ (s ↗ p) ≡ ⨆ (t ↗ q)
    Cofinal→⨆-≡ {s} {t} {p} {q} cof cof′ = ⊑-antisym (Cofinal→⨆-⊑ cof) (Cofinal→⨆-⊑ cof′)


  -- Intensionally Directed-Complete (Pointed) Partial Order
  record D-CompletePartialOrder : Set (ℓ ⊔ ℓ′) where

    open PartialOrder.PartialOrder PO renaming (_≤_ to _⊑_; ≤-refl to ⊑-refl;
         ≤-antisym to ⊑-antisym; ≤-trans to ⊑-trans; ≤-prop to ⊑-prop; A-set to 𝔼-set) public

    field
      ⊥ : A
      ⊥⊑x : ∀ {x : A} → ⊥ ⊑ x
      ⨆ : DirSeq PO → A
      ⨆-ub : ∀ (n : ℕ) → t ⟨ n ⟩ ⊑ ⨆ t
      ⨆-lub : ∀ {b : A} → (∀ (n : ℕ) → t ⟨ n ⟩  ⊑ b) → ⨆ t ⊑ b

    DirSeq-≡ : ∀ {s t : ℕ → A} {dirₛ : Dir PO s} {dirₜ : Dir PO t}
             → (s ≡ t) → ⨆ (s ⇗ dirₛ) ≡ ⨆ (t ⇗ dirₜ)
    DirSeq-≡ {s} {t} s≡t = ⊑-antisym (⨆-lub (λ n → ⊑-trans (subst (λ u → s n ⊑ u n) s≡t ⊑-refl) (⨆-ub n)))
                                     (⨆-lub (λ n → ⊑-trans (subst (λ u → t n ⊑ u n) (sym s≡t) ⊑-refl) (⨆-ub n))) 

    ⨆-const : ∀ {x : A}{dir : Dir PO (λ _ → x)} → ⨆ ((λ _ → x) ⇗ dir) ≡ x
    ⨆-const {x}{dir} = ⊑-antisym (⨆-lub (λ n → ⊑-refl)) (⨆-ub {t = (λ _ → x) ⇗ dir } 0) 

    Cofinal→⨆-⊑ : ∀ {s t : Seq PO} {p : Dir PO s} {q : Dir PO t} → Cofinal PO s t → ⨆ (s ⇗ p) ⊑ ⨆ (t ⇗ q)
    Cofinal→⨆-⊑{s}{t}{p}{q} cof = cofinal-lubs PO s t cof 
      record
        { ub    = ⨆ (s ⇗ p)
        ; is-ub = ⨆-ub 
        ; is-l  = ⨆-lub
        } 
      record
        { ub    = ⨆ (t ⇗ q)
        ; is-ub = ⨆-ub 
        ; is-l  = ⨆-lub
        } 

    Cofinal→⨆-≡ : ∀ {s t : Seq PO} {p : Dir PO s} {q : Dir PO t} → Cofinal PO s t → Cofinal PO t s → ⨆ (s ⇗ p) ≡ ⨆ (t ⇗ q)
    Cofinal→⨆-≡ {s} {t} {p} {q} cof cof′ = ⊑-antisym (Cofinal→⨆-⊑ cof) (Cofinal→⨆-⊑ cof′)


  -- Extensionaly Directed-Complete (Pointed) Partial Order
  record ‖D-CompletePartialOrder‖ : Set (ℓ ⊔ ℓ′) where

    open PartialOrder.PartialOrder PO renaming (_≤_ to _⊑_; ≤-refl to ⊑-refl; ≤-antisym to ⊑-antisym; ≤-trans to ⊑-trans
                                               ; ≤-prop to ⊑-prop; A-set to 𝔼-set) public

    field
      ⊥ : A
      ⊥⊑x : ∀ {x : A} → ⊥ ⊑ x
      ⨆ : ‖DirSeq‖ PO → A
      ⨆-ub : ∀ (n : ℕ) → ‖t‖ ⟪ n ⟫ ⊑ ⨆ ‖t‖
      ⨆-lub : ∀ {b : A} → (∀ (n : ℕ) → ‖t‖ ⟪ n ⟫  ⊑ b) → ⨆ ‖t‖ ⊑ b

  open PartialOrder.PartialOrder PO using () renaming (_≤_ to _⊑_)

  -- extensional directed completeness implies intensional directed completeness
  ‖DCPO‖→DCPO : ‖D-CompletePartialOrder‖ → D-CompletePartialOrder
  ‖DCPO‖→DCPO ‖DCPO‖ =
    record
      { ⊥ = ⊥
      ; ⊥⊑x = ⊥⊑x
      ; ⨆ = λ { (seq ⇗ dir) → ⨆ ((λ z → seq z) ‖⇗‖ λ n m → ∣ dir n m ∣) }
      ; ⨆-ub = ⨆-ub 
      ; ⨆-lub = ⨆-lub 
      }
    where open ‖D-CompletePartialOrder‖ ‖DCPO‖

  -- directed completeness implies chain completeness
  DCPO→ωCPO : D-CompletePartialOrder → ω-CompletePartialOrder
  DCPO→ωCPO DCPO =
    record
      { ⊥ = ⊥
      ; ⊥⊑x = ⊥⊑x
      ; ⨆ = ⨆ ∘ IncSeq→DirSeq
      ; ⨆-ub = ⨆-ub 
      ; ⨆-lub = ⨆-lub 
      }
    where open D-CompletePartialOrder DCPO

  -- intensional directed completeness implies extensional directed completeness under countable choice
  DCPO→‖DCPO‖ : ACω → D-CompletePartialOrder → ‖D-CompletePartialOrder‖
  DCPO→‖DCPO‖ acω DCPO =
    record
      { ⊥ = ⊥
      ; ⊥⊑x = ⊥⊑x
      ; ⨆ = λ t → Lub.ub (‖⨆‖-Lub t)
      ; ⨆-ub = λ {t} → Lub.is-ub (‖⨆‖-Lub t)
      ; ⨆-lub = λ {t} → Lub.is-l (‖⨆‖-Lub t)
      }
    where
      open D-CompletePartialOrder DCPO
      
      ⨆-Lub : ∀ (seq : Seq PO) → Dir PO seq → Lub PO seq
      ⨆-Lub seq dir = record
                         { ub = ⨆ (seq ⇗ dir)
                         ; is-ub = ⨆-ub
                         ; is-l = ⨆-lub
                         }

      acω′ = ACω→ACω′ acω

      ‖⨆‖-Lub : ∀ (s : ‖DirSeq‖ PO) → Lub PO (‖DirSeq‖.seq s)
      ‖⨆‖-Lub (seq ‖⇗‖ dir) = ‖‖-Rec (Lub-prop PO seq)
                                      (λ dir′ → ⨆-Lub seq dir′)
                                      (acω′ _ (λ n → acω′ _ (λ m → dir n m)))



Triv-ω-CompletePartialOrder : ω-CompletePartialOrder TrivPartialOrder
Triv-ω-CompletePartialOrder =
  record
    { ⊥ = tt
    ; ⊥⊑x = tt
    ; ⨆ = λ s → tt
    ; ⨆-ub = λ n → tt
    ; ⨆-lub = λ b → tt
    }

private
  variable
    PO PO′ : PartialOrder A

module _ (ωCPO : ω-CompletePartialOrder {ℓ} {ℓ′} {A} PO) where

  open ω-CompletePartialOrder ωCPO
  open IncSeq

  -- Complete Partial Order on the function space (X → A)
  module _ {ℓ-X : Level} (X : Set ℓ-X) where
    →-ωCPO : ω-CompletePartialOrder (→-PO PO X)
    →-ωCPO = record
              { ⊥ = λ x → ⊥
              ; ⊥⊑x = λ x → ⊥⊑x
              ; ⨆ = λ { (seq ↗ inc) x → ⨆ ((λ n → seq n x) ↗ (λ n → inc n x)) }
              ; ⨆-ub = λ n x → ⨆-ub n
              ; ⨆-lub = λ b x → ⨆-lub (λ n → b n x)
              }

  -- Continuous functions wrt to chains
  module _ (ωCPO′ : ω-CompletePartialOrder {ℓ} {ℓ′} PO′) where
    open  ω-CompletePartialOrder ωCPO′ renaming (⨆ to ⨆′)

    ωCont : MonoFun PO PO′ → Set _
    ωCont (fun ↑ mono) = ∀ (s : IncSeq PO) → ⨆′ ((fun ∘ (seq s)) ↗ (mono ∘ (inc s))) ≡ fun (⨆ s)

    record ContFun : Set (ℓ ⊔ ℓ′) where
      constructor _↝_
      field
        monoFun : MonoFun PO PO′

      open MonoFun monoFun public

      field
        cont : ωCont monoFun

    infix 3 _↝_

module _ (DCPO : D-CompletePartialOrder {ℓ} {ℓ′} {A} PO) where

  open D-CompletePartialOrder DCPO
  open DirSeq

  -- Complete Partial Order on the function space (X → A)
  module _ {ℓ-X : Level} (X : Set ℓ-X) where
    →-DCPO : D-CompletePartialOrder (→-PO PO X)
    →-DCPO = record
              { ⊥ = λ x → ⊥
              ; ⊥⊑x = λ x → ⊥⊑x
              ; ⨆ = λ { (seq ⇗ dir) x →
                  ⨆ ((λ n → seq n x) ⇗ λ m n →
                        (proj₁ $ dir m n) ,                    
                        ((proj₁ $ proj₂ $ dir m n) x) ,
                        ((proj₂ $ proj₂ $ dir m n) x)) }
              ; ⨆-ub  = λ n x → ⨆-ub n
              ; ⨆-lub = λ b x → ⨆-lub (λ n → b n x)
              }

  -- Continuous functions w.r.t. intensional directed completeness
  module _ (DCPO′ : D-CompletePartialOrder {ℓ} {ℓ′} PO′) where
    open  D-CompletePartialOrder DCPO′ renaming (⨆ to ⨆′; ⊑-antisym to ⊑′-antisym; ⊑-refl to ⊑′-refl; ⨆-ub to ⨆′-ub; ⨆-lub to ⨆′-lub) 
    
    Cont : MonoFun PO PO′ → Set _
    Cont (fun ↑ mono) = ∀ (s : DirSeq PO) → ⨆′ (DirSeq-mono s (fun ↑ mono)) ≡ fun (⨆ s)

    record D-ContFun : Set (ℓ ⊔ ℓ′) where
      constructor _↝ᵈ_

      field
        monoFun : MonoFun PO PO′

      open MonoFun monoFun public

      field
        cont : Cont monoFun

    infix 3 _↝ᵈ_

module _ (‖DCPO‖ : ‖D-CompletePartialOrder‖ {ℓ} {ℓ′} PO) (‖DCPO′‖ : ‖D-CompletePartialOrder‖ {ℓ} {ℓ′} PO′) where
  open ‖D-CompletePartialOrder‖ ‖DCPO‖
  open ‖D-CompletePartialOrder‖ ‖DCPO′‖ renaming (⨆ to ⨆′)
  open ‖DirSeq‖

  -- Continuous functions w.r.t. extensional directed completeness
    
  ‖Cont‖ : MonoFun PO PO′ → Set _
  ‖Cont‖ (fun ↑ mono) = ∀ {s : ‖DirSeq‖ PO} → ⨆′ (‖DirSeq‖-mono s (fun ↑ mono)) ≡ fun (⨆ s) 

  record ‖D-ContFun‖ : Set (ℓ ⊔ ℓ′) where
    constructor _↝ᵈ_

    field
      monoFun : MonoFun PO PO′

    open MonoFun monoFun public

    field
      cont : ‖Cont‖ monoFun

  infix 3 _↝ᵈ_

private
  variable
    DCPO DCPO′ : D-CompletePartialOrder PO

-- Intensional directed continuity implies chain continuity
Cont→ωCont : ∀ (mfun : MonoFun PO PO′)
             → Cont DCPO DCPO′ mfun
             → ωCont (DCPO→ωCPO PO DCPO) (DCPO→ωCPO PO′ DCPO′) mfun
Cont→ωCont {PO = PO} {PO′ = PO′} {DCPO = DCPO} {DCPO′ = DCPO′} (fun ↑ mono) cont s =
  trans (D-CompletePartialOrder.Cofinal→⨆-≡ DCPO′ (λ n → n ,  ⊑′-refl ) λ n → n , ⊑′-refl)
        (cont (IncSeq→DirSeq s))
  where
    open  D-CompletePartialOrder DCPO′ renaming (⊑-refl to ⊑′-refl) 


-- Intensional directed continuity implies extensional directed continuity under countable choice
Cont→‖Cont‖ : ∀ (acω : ACω) (mfun : MonoFun PO PO′)
              → Cont DCPO DCPO′ mfun
              → ‖Cont‖ (DCPO→‖DCPO‖ PO acω DCPO) (DCPO→‖DCPO‖ PO′ acω DCPO′) mfun
Cont→‖Cont‖ {PO = PO} {PO′ = PO′} {DCPO = DCPO} {DCPO′ = DCPO′} acω (fun ↑ mono) cont {seq ‖⇗‖ dir} =
  ‖‖-Rec 𝔼′-set
          (λ dir′ → begin
                      ‖⨆‖′ (‖DirSeq‖-mono {PO = PO} (seq ‖⇗‖ dir) (fun ↑ mono))
                    ≡⟨ ⊑′-antisym (‖⨆‖′-lub {‖DirSeq‖-mono {PO = PO} (seq ‖⇗‖ dir) (fun ↑ mono)}
                                             (λ n → ⨆′-ub n))
                                  (⨆′-lub (λ n → ‖⨆‖′-ub {‖DirSeq‖-mono {PO = PO} (seq ‖⇗‖ dir) (fun ↑ mono)}
                                                          n)) ⟩
                       ⨆′ (DirSeq-mono {PO = PO} (seq ⇗ dir′) (fun ↑ mono))
                    ≡⟨ cont (seq ⇗ dir′) ⟩
                       fun (⨆ (seq ⇗ dir′))
                    ≡⟨ cong fun (⊑-antisym (⨆-lub (λ n → ‖⨆‖-ub {seq ‖⇗‖ dir} n))
                                           (‖⨆‖-lub {seq ‖⇗‖ dir} (λ n → ⨆-ub n))) ⟩
                       fun (‖⨆‖ (seq ‖⇗‖ dir))
                    ∎)
          (acω′ _ (λ n → acω′ _ (λ m → dir n m)))

  where
    open D-CompletePartialOrder DCPO using (⨆; ⨆-ub; ⨆-lub; ⊑-antisym)
    open D-CompletePartialOrder DCPO′ using () renaming (⨆ to ⨆′; ⨆-ub to ⨆′-ub; ⨆-lub to ⨆′-lub
                                                        ; 𝔼-set to 𝔼′-set; ⊑-antisym to ⊑′-antisym)
    open ‖D-CompletePartialOrder‖ (DCPO→‖DCPO‖ PO acω DCPO) using () renaming (⨆ to ‖⨆‖; ⨆-ub to ‖⨆‖-ub; ⨆-lub to ‖⨆‖-lub)
    open ‖D-CompletePartialOrder‖ (DCPO→‖DCPO‖ PO′ acω DCPO′) using () renaming (⨆ to ‖⨆‖′; ⨆-ub to ‖⨆‖′-ub; ⨆-lub to ‖⨆‖′-lub)
    acω′ = ACω→ACω′ acω


module LeastFixpoints (ωCPO : ω-CompletePartialOrder {ℓ} {ℓ′} {A} PO) where

  open ω-CompletePartialOrder ωCPO
  open IncSeq
  open ContFun

  _^_ : (f : A → A) → ℕ → (A → A)
  f ^ zero = id
  f ^ suc n = λ x → f ((f ^ n) x)

  ^-inc : ∀ (F : MonoFun PO PO) (n : ℕ) → ((MonoFun.fun F) ^ n) ⊥ ⊑ ((MonoFun.fun F) ^ (suc n)) ⊥
  ^-inc (f ↑ f-mono-⊑) zero = ⊥⊑x
  ^-inc (f ↑ f-mono-⊑) (suc n) = f-mono-⊑ (^-inc (f ↑ f-mono-⊑) n)

  -- Least fixpoint operator μ
  μ : (F : ContFun ωCPO ωCPO) → A
  μ (f ↑ f-mono-⊑ ↝ f-cont-⨆) = ⨆ ((λ n → (f ^ n) ⊥) ↗ ^-inc (f ↑ f-mono-⊑))

  μ-fix : ∀ (F : ContFun ωCPO ωCPO) → (fun F) (μ F) ≡ μ F
  μ-fix (f ↑ f-mono-⊑ ↝ f-cont-⨆) = begin
                                       f (μ (f ↑ f-mono-⊑ ↝ f-cont-⨆))
                                     ≡⟨⟩
                                       f (⨆ ((λ n → (f ^ n) ⊥) ↗ ^-inc (f ↑ f-mono-⊑)))
                                     ≡⟨ sym (f-cont-⨆ ( ((λ n → (f ^ n) ⊥) ↗ ^-inc (f ↑ f-mono-⊑)))) ⟩ 
                                       ⨆ ((λ n → f ((f ^ n) ⊥)) ↗ f-mono-⊑ ∘ ^-inc (f ↑ f-mono-⊑))
                                     ≡⟨ sym ⨆ₙ≡⨆ₛₙ ⟩
                                       ⨆ ((λ n → (f ^ n) ⊥) ↗ ^-inc (f ↑ f-mono-⊑))
                                     ≡⟨⟩
                                       μ (f ↑ f-mono-⊑ ↝ f-cont-⨆)
                                     ∎
    where
      ⨆ₙ≡⨆ₛₙ : ⨆ ((λ n → (f ^ n) ⊥) ↗ ^-inc (f ↑ f-mono-⊑)) ≡
                ⨆ ((λ n → f ((f ^ n) ⊥)) ↗ f-mono-⊑ ∘ ^-inc (f ↑ f-mono-⊑))
      ⨆ₙ≡⨆ₛₙ = ⊑-antisym (⨆-lub (λ n → ⊑-trans (^-inc (f ↑ f-mono-⊑) n) (⨆-ub n)))
                          (⨆-lub (λ n → ⨆-ub (suc n)))

  -- μ F is a least pre-fixpoint
  μ-lpf : ∀ (F : ContFun ωCPO ωCPO) (x : A) → (fun F) x ⊑ x → μ F ⊑ x
  μ-lpf (f ↑ f-mono-⊑ ↝ f-cont-⨆) x fx⊑x =
    ⨆-lub fn⊥⊑x 
    where
      fn⊥⊑x : ∀ (n : ℕ) → (f ^ n) ⊥ ⊑ x
      fn⊥⊑x zero = ⊥⊑x
      fn⊥⊑x (suc n) = ⊑-trans (f-mono-⊑ (fn⊥⊑x n)) (fx⊑x)

  -- hence, a least fixpoint
  μ-lf : ∀ (F : ContFun ωCPO ωCPO) (x : A) → ((fun F) x ≡ x) → μ F ⊑ x
  μ-lf F x fx≡x = μ-lpf F x (subst (λ y → fun F x  ⊑ y) fx≡x ⊑-refl)

 
