{-# OPTIONS --cubical --safe #-}

open import Level using (Level)
open import Function using (_∘_)
open import Relation.Nullary using (yes; no; ¬_)
open import Data.Nat using (ℕ; zero; suc) renaming (_+_ to _+ᴺ_; _≤_ to _≤ᴺ_; z≤n to z≤ᴺn; s≤s to s≤ᴺs; _≤?_ to _≤ᴺ?_)
open import Data.Nat.Properties using () renaming (≤-refl to ≤ᴺ-refl; ≤-trans to ≤ᴺ-trans)
open import Data.Empty using (⊥-elim)
open import Data.Product using (_×_; Σ; _,_; ∃-syntax; proj₁; proj₂)

open import CubicalIdentity using (_≡_; [_]_≡_; refl; sym; cong; congP; cong-app; trans; transport
                                  ; subst; subst-refl; subst2; subst-const; subst≡→[]≡; →-≡)
open import Sets

open import PartialOrder
open import Cantor

--*
{-
  This module introduces the notion of chain completion.
-}
--*

module ChainCompletion {ℓ : Level} {A : Set ℓ} (PO : PartialOrder {ℓ} A) where

open PartialOrder.PartialOrder PO

private
  variable
    ℓ-P ℓ-B : Level
    B : Set ℓ-B
    s t u : ‖DirSeq‖ PO

_≲_ : ‖DirSeq‖ PO → ‖DirSeq‖ PO → Set ℓ
(s ‖⇗‖ dirₛ) ≲ (t ‖⇗‖ dirₜ) = ∀ n → ‖ ∃[ m ] (s n ≤ t m) ‖

≲-prop : IsProp (s ≲ t)
≲-prop = IsProp-∀ (λ _ → ‖‖-prop)

≲-refl : s ≲ s
≲-refl = λ n → ∣ n , ≤-refl ∣

≲-trans : s ≲ t → t ≲ u → s ≲ u
≲-trans s≲t t≲u = λ n → ‖‖-Rec ‖‖-prop
                               (λ { (m , sn≤tm) → ‖‖-Rec ‖‖-prop
                                                         (λ { (k , tm≤uk) → ∣ k , (≤-trans sn≤tm tm≤uk) ∣ })
                                                         (t≲u m) })
                               (s≲t n)


data Ã : Set ℓ where
  [_]~ : (‖DirSeq‖ PO) → Ã
  Ã-eq : s ≲ t → t ≲ s → [ s ]~ ≡ [ t ]~
  Ã-Set : IsSet Ã

Ã-Elim : ∀ {P : Ã → Set ℓ-P}
           (P-[]~ : ∀ s → P [ s ]~)
           (P-eq : ∀ {s t : ‖DirSeq‖ PO} (s≲t : s ≲ t) (t≲s : t ≲ s)
                   → subst P (Ã-eq s≲t t≲s) (P-[]~ s) ≡ (P-[]~ t))
           (P-Set : ∀ x → IsSet (P x))
         → (∀ x → P x)
Ã-Elim {ℓ-P} {P} P-[]~ P-eq P-Set [ s ]~ = P-[]~ s
Ã-Elim {ℓ-P} {P} P-[]~ P-eq P-Set (Ã-eq s≲t t≲s i) = subst≡→[]≡ {P = P} (P-eq s≲t t≲s) i
Ã-Elim {ℓ-P} {P} P-[]~ P-eq P-Set (Ã-Set {x} {y} p q i j) = Set→[]≡ Ã-Set P-Set
                                                                    (congP (Ã-Elim P-[]~ P-eq P-Set) p)
                                                                    (congP (Ã-Elim P-[]~ P-eq P-Set) q)
                                                                    i j

Ã-Elim-Prop : ∀ {P : Ã → Set ℓ-P}
                (P-[]~ : ∀ s → P [ s ]~)
                (P-Prop : ∀ x → IsProp (P x))
              → (∀ x → P x)
Ã-Elim-Prop P-[]~ P-Prop = Ã-Elim P-[]~ (λ _ _ → P-Prop _ _ _) (λ x → prop-is-set (P-Prop x))

Ã-Rec : ∀ (f : ‖DirSeq‖ PO → B)
          (f-≲ : ∀ {s t : ‖DirSeq‖ PO} → (s ≲ t) → (t ≲ s)
                 → f s ≡ f t)
          (B-Set : IsSet B)
        → (Ã → B)
Ã-Rec f f-≲ B-Set = Ã-Elim f (λ {s} {t} s≲t t≲s → trans (subst-const (Ã-eq {s} {t} s≲t t≲s)) (f-≲ s≲t t≲s)) (λ _ → B-Set)

Ã-Rec-Prop : ∀ (f : ‖DirSeq‖ PO → B)
               (B-Set : IsProp B)
             → (Ã → B)
Ã-Rec-Prop f B-Prop = Ã-Rec f (λ _ _ → B-Prop _ _) (prop-is-set B-Prop)

Ã-Rec2 : ∀ (f : ‖DirSeq‖ PO → ‖DirSeq‖ PO → B)
           (f-≲ : ∀ {s s′ t t′ : ‖DirSeq‖ PO} → (s ≲ s′) → (s′ ≲ s) → (t ≲ t′) → (t′ ≲ t)
                  → f s t ≡ f s′ t′)
           (B-Set : IsSet B)
         → (Ã → Ã → B)
Ã-Rec2 f f-≲ B-Set = Ã-Rec (λ s → Ã-Rec (λ t → f s t)
                                        (λ {t} {t′} t≲t′ t′≲t → f-≲ (≲-refl {s}) (≲-refl {s}) t≲t′ t′≲t)
                                        B-Set)
                           (λ {s} {s′} s≲s′ s′≲s → →-≡ (Ã-Elim-Prop (λ t → f-≲ s≲s′ s′≲s (≲-refl {t}) (≲-refl {t}))
                                                                    (λ _ → B-Set)))
                           (IsSet-∀ (λ _ → B-Set))

LE : Ã → Ã → Proposition {ℓ}
LE = Ã-Rec2 (λ s t → (s ≲ t) , ≲-prop {s} {t})
            (λ {s} {s′} {t} {t′} s≲s′ s′≲s t≲t′ t′≲t
             → Σ-Prop-≡ IsProp-Prop (Prop-≡ (≲-prop {s} {t}) (≲-prop {s′} {t′})
                                            (λ s≲t → ≲-trans {s′} {s} {t′} s′≲s (≲-trans {s} {t} {t′} s≲t t≲t′))
                                            λ s′≲t′ → ≲-trans {s} {s′} {t} s≲s′ (≲-trans {s′} {t′} {t} s′≲t′ t′≲t)))
            Proposition-Set

PO-≾ : PartialOrder Ã
PO-≾ = record
         { _≤_ = λ s t → proj₁ (LE s t)
         ; ≤-refl = λ {x} → Ã-Elim-Prop {P = λ x′ → proj₁ (LE x′ x′)} (λ s → ≲-refl {s}) (λ x′ → (proj₂ (LE x′ x′))) x
         ; ≤-antisym = λ {x} {y} → Ã-Elim-Prop {P = λ x′ → proj₁ (LE x′ y) → proj₁ (LE y x′) → x′ ≡ y}
                                               (λ s →
                                               Ã-Elim-Prop {P = λ y′ → proj₁ (LE [ s ]~ y′) → proj₁ (LE y′ [ s ]~) → [ s ]~ ≡ y′}
                                                           (λ t → Ã-eq)
                                                           ((λ _ → IsProp-∀ (λ _ → IsProp-∀ (λ _ → Ã-Set))))
                                                           y)
                                               (λ _ → IsProp-∀ (λ _ → IsProp-∀ (λ _ → Ã-Set)))
                                               x
         ; ≤-trans = λ {x} {y} {z} → Ã-Elim-Prop {P = λ x′ → proj₁ (LE x′ y) → proj₁ (LE y z) → proj₁ (LE x′ z)}
                                                 (λ s →
                                                 Ã-Elim-Prop {P = λ y′ → proj₁ (LE [ s ]~ y′) → proj₁ (LE y′ z) → proj₁ (LE [ s ]~ z)}
                                                             (λ t →
                                                             Ã-Elim-Prop {P = λ z′ → s ≲ t → proj₁ (LE [ t ]~ z′) → proj₁ (LE [ s ]~ z′)}
                                                                         (λ u → ≲-trans {s} {t} {u})
                                                                         ((λ z′ → IsProp-∀ (λ _ → IsProp-∀ (λ _ → proj₂ (LE [ s ]~ z′)))))
                                                                         z)
                                                             ((λ _ → IsProp-∀ (λ _ → IsProp-∀ (λ _ → proj₂ (LE [ s ]~ z)))))
                                                             y)
                                                 (λ x′ → IsProp-∀ (λ _ → IsProp-∀ (λ _ → proj₂ (LE x′ z))))
                                                 x
         ; ≤-prop = λ {s} {t} → proj₂ (LE s t)
         }

open PartialOrder.PartialOrder PO-≾ using () renaming (_≤_ to _≾_; ≤-refl to ≾-refl; ≤-antisym to ≾-antisym
                                                      ; ≤-trans to ≾-trans; ≤-prop to ≾-prop) public

[]~-surj : IsSurj [_]~
[]~-surj = Ã-Elim-Prop (λ s → ∣ s , refl ∣) (λ _ → ‖‖-prop)

ℕ→[]~ : (ℕ → ‖DirSeq‖ PO) → (ℕ → Ã)
ℕ→[]~ f n = [ f n ]~

ℕ→[]~-surj : ACω → IsSurj ℕ→[]~
ℕ→[]~-surj acω f = ‖‖-Rec ‖‖-prop (λ { (g , p) → ∣ g , →-≡ p ∣})
                          (acω _ (λ n → []~-surj (f n)))

≲-DirSeq : Set ℓ
≲-DirSeq = Σ (ℕ → ‖DirSeq‖ PO)
             (λ seq → ∀ n m → (∃[ k ] ((seq n ≲ seq k) × (seq m ≲ seq k))))

≲-DirSeq-≾ : ≲-DirSeq → DirSeq PO-≾
≲-DirSeq-≾ (seq , dir) = (λ n → [ seq n ]~) ⇗ dir

≲-DirSeq-≾-surj : ACω → ∀ (s : DirSeq PO-≾) → ‖ ∃[ s′ ] (DirSeq.seq (≲-DirSeq-≾ s′) ≡ DirSeq.seq s) ‖ 
≲-DirSeq-≾-surj acω (seq ⇗ dir) = ‖‖-map (λ { (s , p) → (s , (λ n m → proj₁ (dir n m) , (subst2 (λ t u → t ≾ u)
                                                                                                (sym (cong-app p n))
                                                                                                (sym (cong-app p (proj₁ (dir n m))))
                                                                                                (proj₁ (proj₂ (dir n m))))
                                                                                      , (subst2 (λ t u → t ≾ u)
                                                                                                (sym (cong-app p m))
                                                                                                (sym (cong-app p (proj₁ (dir n m))))
                                                                                                (proj₂ (proj₂ (dir n m))))))
                                                        , p })
                                         (ℕ→[]~-surj acω seq)

≲-DirSeq-mono : ≲-DirSeq → Σ (‖DirSeq‖ PO → ‖DirSeq‖ PO) (λ f → ∀ {x y : ‖DirSeq‖ PO} → x ≲ y → f x ≲ f y) → ≲-DirSeq
≲-DirSeq-mono (seq , dir) (fun , mono) = fun ∘ seq , λ n m → (proj₁ (dir n m)) , (mono (proj₁ (proj₂ (dir n m)))
                                                                               , (mono (proj₂ (proj₂ (dir n m)))))
