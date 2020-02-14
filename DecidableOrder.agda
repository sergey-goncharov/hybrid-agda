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

open import CubicalIdentity using (_≡_; refl; sym; cong; subst; subst2; →-≡; builtin-to-≡)
open CubicalIdentity.≡-Reasoning
open import Sets

open import PartialOrder
open import CompletePartialOrder


--*
{-
   A connection between truncated directed cpo and omega-cpo 
-}
--*

module DecidableOrder where

private
  variable
    ℓ ℓ′ : Level
    A B : Set ℓ

module _ (PO : PartialOrder {ℓ} {ℓ′} A) where

  private
    variable
      s : IncSeq PO
      t : ‖DirSeq‖ PO

  open PartialOrder.PartialOrder PO using () renaming (_≤_ to _⊑_)

  module _ (t : ‖DirSeq‖ PO) where

    -- bounded search : induction friendly version
    b-search' : ∀ (n : ℕ) → (P : ℕ → Set ℓ′) → (∀ (n : ℕ) → Dec (P n)) → ∀ (c : ℕ)  → P (n +ᴺ c)
      → ∃[ m ] (P (m +ᴺ c) × ∀ (k : ℕ) → (suc k) ≤ᴺ m → ¬ P (k +ᴺ c))
    b-search' zero P dec c Pc = 0 , Pc , (λ k sk≤0 Pc+k → contradiction sk≤0 λ ()) 
    b-search' (suc n) P dec c Pc+n with dec c
    ... | yes p = 0 , (p , (λ k sk≤0 Pk+c → contradiction sk≤0 λ ()))
    ... | no ¬p with b-search' n P dec (suc c) (subst P (sym (builtin-to-≡ (+-suc n c))) Pc+n)
    ... | m , Pm+sc , r  = suc m , subst P (builtin-to-≡ (+-suc m c)) Pm+sc , λ k sk≤sm Pk+c →  h k (≤ᴺ-pred sk≤sm) Pk+c
      where
         h : ∀ (k : ℕ) →  (k ≤ᴺ m) → (P (k +ᴺ c)) → Data.Empty.⊥
         h zero k≤m Pk+c = ¬p Pk+c
         h (suc k) k≤m Pk+c = r k k≤m (subst P (sym (builtin-to-≡ (+-suc k c))) Pk+c)

    ∃‖‖→∃ : ∀ (P : ℕ → Set ℓ′) → (∀ (n : ℕ) → Dec (P n)) → ∃[ n ] ‖ P n ‖ → ∃[ n ] P n
    ∃‖‖→∃ P dec (n , ‖Pn‖) with (dec n)
    ... | yes p = n , p
    ... | no ¬p = n , ⊥-elim (‖‖-Rec (λ ()) ¬p ‖Pn‖)

    -- bounded search : target version
    b-search : ∀ (P : ℕ → Set ℓ′) → (∀ (n : ℕ) → Dec (P n)) → ∃[ n ] P n
      → ∃[ m ] (P m × ∀ (k : ℕ) → (suc k) ≤ᴺ m → ¬ P k)
    b-search P dec (n , Pn) with b-search' n P dec 0 (subst P (sym (builtin-to-≡ (+-identityʳ n))) Pn) 
    b-search P dec (n , Pn) | m , Pm+0 , p =
      m , subst P (builtin-to-≡ (+-identityʳ m)) Pm+0 , λ k sk≤m Pk → p k sk≤m (subst P (sym (builtin-to-≡ (+-identityʳ k))) Pk)


    b-search-uniq : ∀ (P : ℕ → Set ℓ′) → (dec : ∀ (n : ℕ) → Dec (P n)) → (n m : ℕ)
      → (P n × ((k : ℕ) → suc k ≤ᴺ n → ¬ P k)) → (P m × ((k : ℕ) → suc k ≤ᴺ m → ¬ P k)) → n ≡ m
    b-search-uniq P dec zero zero p q = refl
    b-search-uniq P dec zero (suc m) p q = ⊥-elim (proj₂ q zero (s≤ᴺs z≤ᴺn) (proj₁ p))
    b-search-uniq P dec (suc n) zero p q = ⊥-elim (proj₂ p zero (s≤ᴺs z≤ᴺn) (proj₁ q))
    b-search-uniq P dec (suc n) (suc m) p q =
      cong suc (b-search-uniq (P ∘ suc) (dec ∘ suc) n m
        (proj₁ p , λ k r → proj₂ p (suc k) (s≤ᴺs r))
        (proj₁ q , λ k r → proj₂ q (suc k) (s≤ᴺs r))
      )

    b-search-uniq' : ∀ (P : ℕ → Set ℓ′) → (dec : ∀ (n : ℕ) → Dec (P n)) → (n m : ℕ)
                     → ‖ (P n × ((k : ℕ) → suc k ≤ᴺ n → ¬ P k)) ‖ → ‖ (P m × ((k : ℕ) → suc k ≤ᴺ m → ¬ P k)) ‖
                     → n ≡ m
    b-search-uniq' P dec n m p′ q′ = ‖‖-Rec (isSetℕ n m)
                                            (λ p →
                                            ‖‖-Rec (isSetℕ n m)
                                                   (λ q → b-search-uniq P dec n m p q)
                                                   q′)
                                            p′

    -- Exercise 3.19. from the HoTT book
 
    recall-ℕ-choice' : ∀ (P : ℕ → Set ℓ′) → (∀ (n : ℕ) → Dec (P n)) → ‖ ∃[ n ] P n ‖
          → ∃[ m ] ‖ (P m × ∀ (k : ℕ) → (suc k) ≤ᴺ m → ¬ P k) ‖
    recall-ℕ-choice' P dec ∃‖nPn‖ = ‖‖-Rec h' (h P dec) ∃‖nPn‖
      where 
        h : ∀ (P : ℕ → Set ℓ′) → (∀ (n : ℕ) → Dec (P n)) → ∃[ n ] P n 
           → ∃[ m ] ‖ (P m × ∀ (k : ℕ) → (suc k) ≤ᴺ m → ¬ P k) ‖
        h P dec (n , Pn) with b-search P dec (n , Pn)
        h P dec (n , Pn) | m , p =  m , ∣ p ∣

        h' : IsProp (∃[ m ] ‖ (P m × ∀ (k : ℕ) → (suc k) ≤ᴺ m → ¬ P k) ‖)
        h' (n , p) (m , q) = Σ-Prop-≡ ‖‖-prop (b-search-uniq' P dec n m p q)
    
    recall-ℕ-choice : ∀ (P : ℕ → Set ℓ′) → (∀ (n : ℕ) → Dec (P n)) → ‖ ∃[ n ] P n ‖ → ∃[ n ] P n
    recall-ℕ-choice P dec ‖∃nPn‖ with (recall-ℕ-choice' P dec  ‖∃nPn‖)
    recall-ℕ-choice P dec ‖∃nPn‖ | m , p = ∃‖‖→∃ P dec (m , (‖‖-map  proj₁ p))

    dirseq-untrunc : (∀ (x y : A) → Dec (x ⊑ y)) → (n m : ℕ) → ∃[ k ] ((t ⟪ n ⟫ ⊑ t ⟪ k ⟫) × (t ⟪ m ⟫ ⊑ t ⟪ k ⟫))
    dirseq-untrunc dec n m =
      recall-ℕ-choice
        (λ k → (t ⟪ n ⟫) ⊑ (t ⟪ k ⟫) × (t ⟪ m ⟫) ⊑ (t ⟪ k ⟫))
        (λ l → (dec (t ⟪ n ⟫) (t ⟪ l ⟫) ×-dec dec (t ⟪ m ⟫) (t ⟪ l ⟫)))
        (t .‖DirSeq‖.dir n m)
        
  -- chain completenss implies directed completeness under decidability of ⊑
  ωCPO→‖DCPO‖ : (∀ (x y : A) → Dec (x ⊑ y)) → ω-CompletePartialOrder PO → ‖D-CompletePartialOrder‖ PO
  ωCPO→‖DCPO‖ dec ωCPO =
    record
      { ⊥ = ⊥
      ; ⊥⊑x = ⊥⊑x
      ; ⨆     = λ t → ⨆ (t-chain t dec)
      ; ⨆-ub  = λ {t} n → ⊑-trans (proj₂ (t-gt t dec n)) (⨆-ub {s = t-chain t dec} (proj₁ (t-gt t dec n))) 
      ; ⨆-lub = λ {t} p → ⨆-lub (λ n → p (σ t dec n)) 
      }
    where
      σ : ‖DirSeq‖ PO → (∀ (x y : A) → Dec (x ⊑ y)) → ℕ → ℕ
      σ t' dec 0 = 0
      σ t' dec (suc n) = proj₁ (dirseq-untrunc t' dec n (σ t' dec n))

      θ : ‖DirSeq‖ PO → (∀ (x y : A) → Dec (x ⊑ y)) → ℕ → A
      θ t' dec = (t' . ‖DirSeq‖.seq) ∘ (σ t' dec)  

      θ-inc : (t' : ‖DirSeq‖ PO) → (dec : ∀ (x y : A) → Dec (x ⊑ y)) → Inc PO (θ t' dec)
      θ-inc t' dec zero = proj₁ (proj₂ (dirseq-untrunc  t' dec 0 (σ t' dec 0)))
      θ-inc t' dec (suc n) = proj₂ (proj₂ (dirseq-untrunc  t' dec (suc n) (σ t' dec (suc n))))

      t-chain : ‖DirSeq‖ PO → (dec : ∀ (x y : A) → Dec (x ⊑ y)) → IncSeq PO
      t-chain t' dec = (θ t' dec) ↗ (θ-inc t' dec)

      t-gt : (t' : ‖DirSeq‖ PO) → (dec : ∀ (x y : A) → Dec (x ⊑ y)) → ∀ (n : ℕ)
             → ∃[ m ] ((t' ⟪ n ⟫) ⊑ (t-chain t' dec) [ m ]) 
      t-gt t' dec n = suc n , proj₁ ( (proj₂ (dirseq-untrunc t' dec n (σ t' dec n))))

      open ω-CompletePartialOrder ωCPO
