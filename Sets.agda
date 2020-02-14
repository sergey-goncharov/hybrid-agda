{-# OPTIONS --cubical --safe #-}

open import Level using (Level ; _⊔_; Lift; lift) renaming (suc to ℓ-suc)
open import CubicalIdentity
open CubicalIdentity.≡-Reasoning
open import Cubical.Foundations.HLevels using (isSetHProp; isOfHLevelΣ; propPi; isSetPi; isOfHLevel→isOfHLevelDep)
open import Cubical.Foundations.Isomorphism using (isoToPath)
open import Data.Product using (Σ; ∃-syntax; _×_; _,_; proj₁; proj₂)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit
open import Data.Empty


--*
{-
  This module introduces the notion of proposition and set.
-
  Furthermore, it provides two statements about when a given Set is a set.
  Many proofs are inspired by or follow directly the proofs from the HoTT book.
-}
--*

-- Dependent h-level over a Set

module Sets where

private
  variable
    ℓ ℓ′ : Level
    A B : Set ℓ

open import Cubical.Data.Nat.Properties public using (isSetℕ) -- reexport isSetℕ

-- The property of being a proposition.
IsProp : Set ℓ → Set ℓ
IsProp A = (x y : A) → x ≡ y

-- A proposition
Proposition : Set (ℓ-suc ℓ)
Proposition {ℓ} = Σ (Set ℓ) (λ A → IsProp A)

-- The property of being a set.
IsSet : Set ℓ → Set ℓ
IsSet A = {x y : A} → IsProp (x ≡ y)

-- Lemma 2.9.6 from the HoTT book
subst→subst-subst : ∀ {x y : A} (p : x ≡ y) {P : A → Set ℓ} {Q : A → Set ℓ′} (f : P x → Q x) (g : P y → Q y)
  → subst (λ x → P x → Q x) p f ≡ g → ∀ (a : P x) → subst Q p (f a) ≡ g (subst P p a)

subst→subst-subst {x = x} p {P} {Q} f g f≡g a =
  (J (λ y′ p′ → ∀ (g′ : P y′ → Q y′) → subst (λ x → P x → Q x) p′ f ≡ g′
              → ∀ (a : P x) → subst Q p′ (f a) ≡ g′ (subst P p′ a)) h p) g f≡g a
    where
      h : (g′ : P x → Q x) → subst (λ z → P z → Q z) refl f ≡ g′ → (a′ : P x)
              → subst Q refl (f a′) ≡ g′ (subst P refl a′)
      h g′ f≡g′ a′ =
        begin
          subst Q refl (f a′)
        ≡⟨ subst-refl Q (f a′) ⟩
          f a′
        ≡⟨ cong-app (trans (sym (subst-refl (λ x → P x → Q x) f)) f≡g′) a′ ⟩
          g′ a′
        ≡⟨ cong g′ (sym (subst-refl P a′)) ⟩
          g′ (subst P refl a′)
        ∎

-- Lemma 2.11.2 from the HoTT book
subst→trans : ∀ {x y z : A} {y≡z : y ≡ z} {x≡y : x ≡ y}
               → subst (λ y → x ≡ y) y≡z x≡y ≡ trans x≡y y≡z
subst→trans {ℓ} {A} {x} {y} {z} {y≡z} {x≡y} =
  J (λ z′ y≡z′ → subst (λ y → x ≡ y) y≡z′ x≡y ≡ trans x≡y y≡z′)
  (trans (transport-refl x≡y) (sym trans-reflʳ)) y≡z

trans-dep : ∀ {A : Set ℓ} (x : A) (g : (y : A) → x ≡ y) (y z : A) (p : y ≡ z)
  → trans (g y) p ≡ g z
trans-dep x g y z p = J (λ z' p' → trans (g y) p' ≡  g z') trans-reflʳ p

-- Lemma 3.3.4 from the HoTT book
prop-is-set : IsProp A → IsSet A
prop-is-set f {x} {y} p q =
  begin
    p
      ≡⟨ trans→sym (trans-dep x (λ y → f x y) x y p) ⟩
    trans (sym (f x x)) (f x y)
      ≡˘⟨ trans→sym (trans-dep x (λ y → f x y) x y q) ⟩
    q
  ∎

-- Theorem 7.2.2 from the HoTT book
module _ (A : Set ℓ) (_ρ_ : A → A → Set ℓ′) (ρ-prop : ∀ {x y : A} → IsProp (x ρ y))
         (ρ-refl : ∀ {x : A} → x ρ x) (ρ-eq : ∀ {x y : A} → x ρ y → x ≡ y) where

  private
    variable
      x y z : A

  -- This proof follows the first proof of Theorem 7.2.2 from the HoTT book
  trans-ρ : ∀ (p : x ≡ x) → trans (ρ-eq ρ-refl) p ≡ ρ-eq ρ-refl
  trans-ρ {x = x} p =
    begin
      trans (ρ-eq ρ-refl) p
        ≡⟨ sym subst→trans ⟩
      subst (λ y → x ≡ y) p (ρ-eq ρ-refl)
        ≡⟨ subst→subst-subst p {P = λ y → x ρ y} {Q = λ y → x ≡ y} ρ-eq ρ-eq
                         (apd (λ y → ρ-eq {x = x} {y = y}) p) ρ-refl ⟩
                          ρ-eq (subst (λ y → x ρ y) p ρ-refl)
        ≡⟨ cong ρ-eq (ρ-prop ((subst (λ y → x ρ y) p ρ-refl)) ρ-refl) ⟩
      ρ-eq ρ-refl
    ∎

  -- A satisfies Axiom K
  p≡refl : ∀ (p : x ≡ x) → p ≡ refl
  p≡refl {x = x} p =
    begin
      p
        ≡⟨ trans→sym (trans-ρ p) ⟩
      trans (sym (ρ-eq ρ-refl)) (ρ-eq ρ-refl)
        ≡⟨ trans-symˡ ⟩
      refl
    ∎

  A-is-set : IsSet A
  A-is-set p q =
    begin
      p
        ≡˘⟨ trans-reflʳ ⟩
      trans p refl
        ≡˘⟨ subst (λ w → trans p (trans (sym p) q) ≡ trans p w) (p≡refl (trans (sym p) q)) refl ⟩
      trans p (trans (sym p) q)
        ≡⟨ trans-trans ⟩
      trans (trans p (sym p)) q
        ≡⟨ subst (λ w → trans (trans p (sym p)) q ≡ trans w q) trans-symʳ refl ⟩
      trans refl q
        ≡⟨ trans-reflˡ ⟩
      q
    ∎

-- IsProp is a proposition
IsProp-Prop : IsProp (IsProp A)
IsProp-Prop f g = λ i x y → prop-is-set f (f x y) (g x y) i

-- Equality characterization for Σ A P if (P a) is a proposition for every (a : A)
Σ-Prop-≡ : ∀ {P : A → Set ℓ} {x y : A} {p : P x} {q : P y} →
             (Py-Prop : IsProp (P y)) → x ≡ y → (x , p) ≡ (y , q)
Σ-Prop-≡ {P = P} {x} {y} {p} {q} Py-Prop x≡y = λ i → (x≡y i) , (subst≡→[]≡ {P = P} (Py-Prop (subst P x≡y p) q) i)

-- Proposition is a set
Proposition-Set : IsSet (Proposition {ℓ})
Proposition-Set {ℓ} {A} {B} = isSetHProp A B

-- Propositional extensionality
Prop-≡ : IsProp A → IsProp B → (A → B) → (B → A) → A ≡ B
Prop-≡ A-Prop B-Prop f g = isoToPath (record
                                        { fun = f
                                        ; inv = g
                                        ; rightInv = λ b → B-Prop _ _
                                        ; leftInv = λ a → A-Prop _ _
                                        })

-- Convert IsSet to a dependent path
Set→[]≡ : ∀ (A-Set : IsSet A) {P : A → Set ℓ} (P-Set : ∀ x → IsSet (P x))
            {x y : A} {x≡y x≡y′ : x ≡ y} {p : P x} {q : P y}
            (p≡q  : [ (λ j → P (x≡y  j)) ] p ≡ q )
            (p≡q′ : [ (λ j → P (x≡y′ j)) ] p ≡ q )
          → [ (λ i → [ (λ j → P (A-Set x≡y x≡y′ i j)) ] p ≡ q) ] p≡q ≡ p≡q′
Set→[]≡ A-Set {P} P-Set {x} {y} {x≡y} {x≡y′} {p} {q} p≡q p≡q′ = isOfHLevel→isOfHLevelDep 2 {B = P}
                                                                                         (λ x p p′ → P-Set x)
                                                                                         p q p≡q p≡q′ (A-Set x≡y x≡y′)

IsProp-⊥ : IsProp ⊥
IsProp-⊥ = λ x () 

IsProp-∀ : ∀ {P : A → Set ℓ} → (∀ x → IsProp (P x)) → IsProp (∀ x → P x)
IsProp-∀ = propPi

IsProp-∀′ : ∀ {P : A → Set ℓ} → (∀ {x} → IsProp (P x)) → IsProp (∀ {x} → P x)
IsProp-∀′ P-Prop = λ p q → →-≡′ (λ {x} → P-Prop {x} p q)

IsSet-∀ : ∀ {P : A → Set ℓ} → (∀ x → IsSet (P x)) → IsSet (∀ x → P x)
IsSet-∀ P-Set = isSetPi (λ x p q → P-Set x) _ _

IsSet-Σ : ∀ {P : A → Set ℓ} → IsSet A → (∀ x → IsSet (P x)) → IsSet (Σ A P)
IsSet-Σ A-Set P-Set = isOfHLevelΣ 2 (λ _ _ → A-Set) (λ x _ _ → P-Set x) _ _

IsProp-× : IsProp A → IsProp B → IsProp (A × B)
IsProp-× A-Prop B-Prop (a , b) (a′ , b′) = ×-≡ (A-Prop a a′) (B-Prop b b′)

-- Truncation
data ‖_‖ (A : Set ℓ) : Set ℓ where
  ∣_∣ : A → ‖ A ‖
  ‖‖-prop : IsProp ‖ A ‖

‖‖-Elim : ∀ {P : ‖ A ‖ → Set ℓ} → (∀ x → IsProp (P x))
         → (∀ a → P ∣ a ∣) → (∀ x → P x)
‖‖-Elim {P = P} P-Prop P-∣∣ ∣ a ∣ = P-∣∣ a
‖‖-Elim {P = P} P-Prop P-∣∣ (‖‖-prop x y i) = subst≡→[]≡ {P = P} (P-Prop y (subst P (‖‖-prop x y)
                                                                                   (‖‖-Elim P-Prop P-∣∣ x))
                                                                          (‖‖-Elim P-Prop P-∣∣ y)) i

‖‖-Rec : IsProp B → (A → B) → (‖ A ‖ → B)
‖‖-Rec B-Prop f = ‖‖-Elim (λ _ → B-Prop) f

‖‖-map : (A → B) → (‖ A ‖ → ‖ B ‖)
‖‖-map f a = ‖‖-Rec  ‖‖-prop (λ x → ∣ f x ∣) a

-- Axiom of Countable Choice
ACω : Set (ℓ-suc ℓ)
ACω {ℓ} = ∀ {X : Set ℓ} (P : ℕ → X → Set ℓ)
          → (∀ (n : ℕ) → ‖ Σ X (λ x → P n x) ‖)
          → ‖ Σ (ℕ → X) (λ f → (n : ℕ) → P n (f n)) ‖

-- Equivalent formulation of ACω
ACω′ : Set (ℓ-suc ℓ)
ACω′ {ℓ} = ∀ (P : ℕ → Set ℓ) → (∀ n → ‖ P n ‖) → ‖ (∀ n → P n) ‖

ACω→ACω′ : ACω → ACω′ {ℓ}
ACω→ACω′ {ℓ} acω P p = ‖‖-Rec ‖‖-prop (λ { (f , Pf) → ∣ Pf ∣})
                              (acω {X = Lift ℓ ⊤} _ (λ n → ‖‖-Rec ‖‖-prop (λ pn → ∣ lift tt , pn ∣) (p n)))

ACω′→ACω : ACω′ → ACω {ℓ}
ACω′→ACω acω′ P p = ‖‖-Rec ‖‖-prop (λ p′ → ∣ (λ n → proj₁ (p′ n)) , (λ n → proj₂ (p′ n)) ∣)
                           (acω′ _ p)

-- Applying ACω twice
ACω2 : Set (ℓ-suc ℓ)
ACω2 {ℓ} = ∀ {X : Set ℓ} (P : ℕ → X → X → Set ℓ)
          → (∀ (n : ℕ) → ‖ Σ X (λ x → Σ X (λ y → P n x y)) ‖)
          → ‖ Σ (ℕ → X) (λ f → Σ (ℕ → X) (λ g → (n : ℕ) → P n (f n) (g n))) ‖

ACω→ACω2 : ACω → ACω2 {ℓ}
ACω→ACω2 acω {X} P p = ‖‖-Rec ‖‖-prop (λ { (f , q) → ∣ f , ((λ n → proj₁ (q n)) , (λ n → proj₂ (q n))) ∣ })
                              (acω (λ n x → Σ X (P n x)) p)

ACωsuc : Set (ℓ-suc ℓ)
ACωsuc {ℓ} = ∀ {X : Set ℓ} (P : ℕ → X → X → Set ℓ)
             → (∀ (n : ℕ) → ‖ Σ X (λ x → Σ X (λ y → P n x y)) ‖)
             → ‖ Σ (ℕ → X) (λ f → ∀ (n : ℕ) → P n (f n) (f (suc n))) ‖

-- Surjectivity
IsSurj : (A → B) → Set _
IsSurj f = ∀ y → ‖ ∃[ x ] (f x ≡ y) ‖

-- Injectivity
IsInj : (A → B) → Set _
IsInj f = ∀ {x y} → f x ≡ f y → x ≡ y
