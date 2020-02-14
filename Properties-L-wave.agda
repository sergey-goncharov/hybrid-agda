{-# OPTIONS --cubical --safe #-}

open import Level using (Level; _⊔_; Lift; lift) renaming (suc to ℓ-suc)
open import Function using (id; _∘_)
open import Data.Nat using (ℕ; suc)
open import Data.Unit using (⊤; tt)
open import Data.Empty renaming (⊥ to 𝟎; ⊥-elim to 𝟎-elim)
open import Data.Product using (Σ; ∃; ∃-syntax; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Nullary using (¬_)

open import CubicalIdentity using (_≡_; refl; sym; cong; cong-app; transport; trans; subst; subst2
                                  ; subst-const; →-≡; ×-≡; subst≡→[]≡)
open CubicalIdentity.≡-Reasoning
open import Sets

open import PartialOrder
open import Monoid
open import MonoidModule

open import Eliminators-L-wave

--*
{-
  Some properties of L̃. 
-}
--*

module Properties-L-wave {ℓ ℓ′ : Level} {M : Monoid} (OM : O-Monoid {ℓ} {ℓ′} M) (A : Set (ℓ ⊔ ℓ′)) (A-Set : IsSet A) where

open Def-L̃ OM A
open O-Monoid OM renaming (PO to PO-≤; A-set to 𝕄-Set)
open Complete-OM-Module-over L̃-COMMo using (▷-sum; ▷-contʳ)

private
  variable
    a b c : 𝕄
    x y z : L̃
    s : DirSeq PO-⊑

-- A characterization of η x ⊑ z
record ηx⊑- {x : A} : Set (ℓ-suc (ℓ ⊔ ℓ′)) where
  field
    ηx⊑a▷z :             (η x ⊑ a ▷ z) ≡ ((a ≡ 𝟘) × (η x ⊑ z))
    ηx⊑⊥   :             (η x ⊑     ⊥) ≡ Lift _ 𝟎
    ηx⊑⨆s :             (η x ⊑   ⨆ s) ≡ ‖ (∃[ n ] (η x ⊑ s ⟨ n ⟩)) ‖
    ηx⊑ηy  : ∀ {y : A} → (η x ⊑   η y) ≡ (x ≡ y)

ηx⊑-≡ : ∀ {x : A} → ηx⊑- {x}
ηx⊑-≡ {x} = record
              { ηx⊑a▷z = λ {a} {z} → begin
                                       η x ⊑ (a ▷ z)
                                     ≡⟨ ηx⊑z≡ηx⊑z ⟩
                                       proj₁ (ηx⊑ (a ▷ z))
                                     ≡⟨ cong proj₁ (ηx⊑a▷z {a} {z}) ⟩
                                       (a ≡ 𝟘 × proj₁ (ηx⊑ z))
                                     ≡⟨ cong (a ≡ 𝟘 ×_) (sym ηx⊑z≡ηx⊑z) ⟩
                                       (a ≡ 𝟘 × η x ⊑ z)
                                     ∎
              ; ηx⊑⊥ = ηx⊑z≡ηx⊑z
              ; ηx⊑⨆s = λ {s} → begin
                                   (η x ⊑ ⨆ s)
                                 ≡⟨ ηx⊑z≡ηx⊑z ⟩
                                   proj₁ (ηx⊑ ⨆ s)
                                 ≡⟨ cong proj₁ (ηx⊑⨆s {s}) ⟩
                                   ‖ ∃[ n ] (proj₁ (ηx⊑ (s ⟨ n ⟩))) ‖
                                 ≡⟨ cong (λ k → ‖ ∃ k ‖) (→-≡ (λ n → sym ηx⊑z≡ηx⊑z)) ⟩
                                   ‖ ∃[ n ] (η x ⊑ (s ⟨ n ⟩)) ‖
                                 ∎
              ; ηx⊑ηy = ηx⊑z≡ηx⊑z
              }
  where
    Prop-MM : M-Module M
    Prop-MM = record
                { 𝔼 = Proposition
                ; _▷_ = _▷P_
                ; ▷-sum = λ { {a} {b} {C , C-Prop}
                          → Σ-Prop-≡ IsProp-Prop
                                     (Prop-≡ (IsProp-× 𝕄-Set (proj₂ (b ▷P (C , C-Prop))))
                                                       (IsProp-× 𝕄-Set C-Prop)
                                                       (λ { (a≡𝟘 , (b≡𝟘 , c))
                                                        → subst2 (λ a′ b′ → a′ + b′ ≡ 𝟘)
                                                                 (sym a≡𝟘) (sym b≡𝟘) +-identityˡ
                                                          , c })
                                                       (λ { (a+b≡𝟘 , c) → proj₁ (a+b≡𝟘→a≡𝟘×b≡𝟘 a+b≡𝟘)
                                                                          , (proj₂ (a+b≡𝟘→a≡𝟘×b≡𝟘 a+b≡𝟘) , c) })) }
                ; ▷-neutrˡ = λ { {B , B-Prop} → Σ-Prop-≡ IsProp-Prop
                                                         (Prop-≡ (IsProp-× 𝕄-Set B-Prop) B-Prop
                                                                 (λ { (𝟘≡𝟘 , b) → b })
                                                                 (λ b → refl , b)) }
                }
      where
        _▷P_ : _
        a ▷P (B , B-Prop) = ((a ≡ 𝟘) × B) , IsProp-× 𝕄-Set B-Prop

    Prop-OMM : Ordered-M-Module OM Prop-MM
    Prop-OMM = record
                 { ⊥ = (Lift (ℓ ⊔ ℓ′) 𝟎) , (λ ())
                 ; PO-⊑ = record
                            { _≤_ = λ { (P , P-Prop) (Q , Q-Prop) → (P → Q) }
                            ; ≤-refl = id
                            ; ≤-antisym = λ { {P , P-Prop} {Q , Q-Prop} f g
                                          → Σ-Prop-≡ IsProp-Prop
                                                     (Prop-≡ P-Prop Q-Prop f g) }
                            ; ≤-trans = λ f g → g ∘ f
                            ; ≤-prop = λ { {P , P-Prop} {Q , Q-Prop}
                                       → IsProp-∀ (λ _ → Q-Prop) }
                            }
                 ; ⊥⊑x = λ ()
                 ; ▷-monoʳ = λ { f (a≡𝟘 , p) → a≡𝟘 , (f p) }
                 ; ▷⊥-mono = λ { _ (_ , lift contradict) → 𝟎-elim contradict }
                 }

    Prop-COMM : Complete-OM-Module OM Prop-OMM
    Prop-COMM = record
                  { ⨆ = λ s → ‖ ∃[ n ] (proj₁ (s ⟨ n ⟩)) ‖ , ‖‖-prop
                  ; ⨆-ub = λ n sn → ∣ n , sn ∣
                  ; ⨆-lub = λ { {s} {P , P-Prop} bnd q′ → ‖‖-Rec P-Prop
                                                                  (λ (n , sn) → bnd n sn)
                                                                  q′ }
                  ; ▷-contʳ = Σ-Prop-≡ IsProp-Prop
                                       (Prop-≡ ‖‖-prop (IsProp-× 𝕄-Set ‖‖-prop)
                                               (‖‖-Rec (IsProp-× 𝕄-Set ‖‖-prop)
                                                       (λ { (n , (a≡𝟘 , sn))
                                                        → a≡𝟘 , ∣ n , sn ∣ }))
                                               (λ { (a≡𝟘 , p′) → ‖‖-Rec ‖‖-prop
                                                                        (λ (n , sn) → ∣ n , (a≡𝟘 , sn) ∣)
                                                                        p′ }))
                  }

    Prop-COMMo : Complete-OM-Module-over A OM Prop-COMM
    Prop-COMMo = record { η = λ y → (x ≡ y) , A-Set }

    L̃-COMMo→Prop-COMMo : Complete-OM-Module-Morphism-over L̃-COMMo Prop-COMMo
    L̃-COMMo→Prop-COMMo = H Prop-COMMo
      where
        open Initial-Complete-OM-Module-over L̃-Initial using (H)

    open Complete-OM-Module-Morphism-over L̃-COMMo→Prop-COMMo using () renaming (fun to ηx⊑_; f-⊑ to ηx⊑-mono
                                                                               ; f-▷ to ηx⊑a▷z; f-⨆ to ηx⊑⨆s)

    ηx⊑z≡ηx⊑z : (η x ⊑ z) ≡ proj₁ (ηx⊑ z)
    ηx⊑z≡ηx⊑z {z} = Prop-≡ ⊑-prop (proj₂ (ηx⊑ z))
                           (λ ηx⊑z → ηx⊑-mono ηx⊑z refl)
                           (L̃-rec z)
      where
        args : Arguments
        args = record
                 { P-L̃ = λ z → proj₁ (ηx⊑ z) → (η x ⊑ z)
                 ; P-⊑ = λ _ _ _ → ⊤
                 ; P-▷ = λ { {z} b ηx⊑z→ηx⊑z (b≡𝟘 , ηx⊑z)
                         → subst (λ b′ → η x ⊑ b′ ▷ z)
                                 (sym b≡𝟘)
                                 (⊑-trans (ηx⊑z→ηx⊑z ηx⊑z) ▷-neutrˡ⃖) }
                 ; P-⊥ = λ ()
                 ; P-⨆ = λ { (p , _) q → ‖‖-Rec ⊑-prop
                                                (λ (n , qn) → ⊑-trans (p n qn) (⨆-ub n))
                                                q }
                 ; P-η = λ y x≡y → subst (λ y′ → η x ⊑ η y′) x≡y ⊑-refl
                 ; P-⊑-antisym = λ _ _ _ _ → →-≡ (λ _ → ⊑-prop _ _)
                 ; P-⊑-prop = λ { _ _ tt tt → refl }
                 }
        elims : Eliminators args
        elims = L̃-Elim args
        open Eliminators elims using (L̃-rec)
