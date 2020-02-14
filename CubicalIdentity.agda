{-# OPTIONS --cubical --safe #-}

open import Level using (Setω)

open import Data.Product using (Σ; _,_; proj₁; proj₂)
open import Function using (id; _∘_)

open import Cubical.Core.Everything renaming (_≡_ to CubicalId)

--*
{-
  This module is the interface to the Cubical Agda Library
  supplying the basic features of Cubical Agda
  and some useful lemmas on identity types.
-}
--*

module CubicalIdentity where

private
  variable
    ℓ ℓ′ ℓ′′ : Level
    A B C : Set ℓ
    P : A → Set ℓ

-- Homogeneous equality
infix 4 _≡_
_≡_ : _
_≡_ = CubicalId

-- Heterogeneous equality
infix 4 [_]_≡_
[_]_≡_ : _
[_]_≡_ = PathP

refl : ∀ {x : A} → x ≡ x
refl {x = x} = λ i → x

sym : ∀ {x y : A} → x ≡ y → y ≡ x
sym x≡y = λ i → x≡y (~ i)

symP : ∀ {P : I → Set ℓ} {x : P i0} {y : P i1} → [ P ] x ≡ y → [ (λ i → P (~ i)) ] y ≡ x
symP x≡y = λ i → x≡y (~ i)

symInv : ∀ {x y : A} (p : x ≡ y) → sym (sym p) ≡ p
symInv x≡y = refl

cong : ∀ {x y : A} (f : A → B) → x ≡ y → f x ≡ f y
cong f x≡y = λ i → f (x≡y i)

cong-refl : ∀ {x : A} {f : A → B} → cong {x = x} f refl ≡ refl
cong-refl = λ i → refl

congP : ∀ {x y : A} (f : ∀ x → P x) (x≡y : x ≡ y) → [ (λ i → P (x≡y i)) ] f x ≡ f y
congP f x≡y = λ i → f (x≡y i)

cong-app : ∀ {f g : A → B} → f ≡ g → ∀ (x : A) → f x ≡ g x
cong-app f≡g x = λ i → f≡g i x

transport : A ≡ B → A → B
transport A≡B x = transp (λ i → A≡B i) i0 x

transport-refl : ∀ (x : A) → transport refl x ≡ x
transport-refl {A = A} x i = transp (λ j → A) i x

-- The induction principle for paths: the J-rule
J : ∀ {x : A} (P : ∀ y → x ≡ y → Set ℓ)
      (d : P x refl) {y : A} (p : x ≡ y)
    → P y p
J P d p = transport (λ i → P (p i) (λ j → p (i ∧ j))) d

-- Applying J twice
J2 : ∀ {A : Set ℓ} {a b : A} (P : ∀ (c′ : A) (a≡c′ : a ≡ c′) (d′ : A) (b≡d′ : b ≡ d′) → Set ℓ)
      (r : P a refl b refl) {c : A} (p : a ≡ c) {d : A} (q : b ≡ d)
    → P c p d q
J2 {ℓ} {A} {a} {b} P r {c} p {d} q =
  J (λ d′ b≡d′ → P c p d′ b≡d′) (J (λ c′ a≡c′ → P c′ a≡c′ b refl) r p) q

J-refl : ∀ {x : A} (P : ∀ y → x ≡ y → Set ℓ)
         (d : P x refl) → J P d refl ≡ d
J-refl P d = transport-refl d

trans : ∀ {x y z : A} → x ≡ y → y ≡ z → x ≡ z
trans {x = x} x≡y y≡z = λ i → hcomp (λ j → λ { (i = i0) → x ; (i = i1) → y≡z j }) (x≡y i)

trans-reflʳ : ∀ {x y : A} {x≡y : x ≡ y} → trans x≡y refl ≡ x≡y
trans-reflʳ {ℓ} {A} {x} {y} {x≡y} = sym (λ k i → hfill (λ j → λ { (i = i0) → x
                                                                ; (i = i1) → y })
                                                       (inS (x≡y i))
                                                       k)

trans-reflˡ : ∀ {y z : A} {y≡z : y ≡ z} → trans refl y≡z ≡ y≡z
trans-reflˡ {ℓ} {A} {y} {z} {y≡z} = J (λ z′ y≡z′ → trans refl y≡z′ ≡ y≡z′) trans-reflʳ y≡z

trans-symˡ : ∀ {x y : A} {x≡y : x ≡ y} → trans (sym x≡y) x≡y ≡ refl
trans-symˡ {ℓ} {A} {x} {y} {x≡y} = J (λ y′ x≡y′ → trans (sym x≡y′) x≡y′ ≡ refl) trans-reflʳ x≡y

trans-symʳ : ∀ {x y : A} {x≡y : x ≡ y} → trans x≡y (sym x≡y) ≡ refl
trans-symʳ {ℓ} {A} {x} {y} {x≡y} = J (λ y′ x≡y′ → trans x≡y′ (sym x≡y′) ≡ refl) trans-reflˡ x≡y

cong2 : ∀ {x x′ : A}{y y′ : B} (f : A → B → C) → x ≡ x′ → y ≡ y′ → f x y ≡ f x′ y′
cong2 {x′ = x′} {y = y} f x≡x′ y≡y′ = trans (cong (λ z →  f z y)  x≡x′) (cong (λ z →  f x′ z) y≡y′)

open import Agda.Builtin.Equality using () renaming (_≡_ to _≡'_; refl to refl')

builtin-to-≡ : ∀ {x y : A} → x ≡' y → x ≡ y
builtin-to-≡ refl' = refl

-- Equational reasoning for homogeneous equality
module ≡-Reasoning where

  infix  1 begin_
  infixr 2 _≡⟨⟩_
  infixr 2 _≡⟨_⟩_
  infixr 2 _≡˘⟨_⟩_
  infix  3 _∎

  begin_ : ∀ {x y : A} → x ≡ y → x ≡ y
  begin x≡y = x≡y

  _≡⟨⟩_ : ∀ (x : A) {y : A} → x ≡ y → x ≡ y
  x ≡⟨⟩ x≡y = x≡y

  _≡⟨_⟩_ : ∀ (x : A) {y z : A} → x ≡ y → y ≡ z → x ≡ z
  x ≡⟨ x≡y ⟩ y≡z = trans x≡y y≡z

  _≡˘⟨_⟩_ : ∀ (x : A) {y z : A} → y ≡ x → y ≡ z → x ≡ z
  _ ≡˘⟨ y≡x ⟩ y≡z = trans (sym y≡x) y≡z

  _∎ : ∀ (x : A) → x ≡ x
  x ∎ = refl

open ≡-Reasoning

trans-trans : ∀ {w x y z : A} {w≡x : w ≡ x} {x≡y : x ≡ y} {y≡z : y ≡ z}
              → trans w≡x (trans x≡y y≡z) ≡ trans (trans w≡x x≡y) y≡z
trans-trans {ℓ} {A} {w} {x} {y} {z} {w≡x} {x≡y} {y≡z} =
  J (λ z′ y≡z′ → trans w≡x (trans x≡y y≡z′) ≡ trans (trans w≡x x≡y) y≡z′)
    (begin
      trans w≡x (trans x≡y refl)
    ≡⟨ cong (trans w≡x) trans-reflʳ ⟩
      trans w≡x x≡y
    ≡⟨ sym trans-reflʳ ⟩
      trans (trans w≡x x≡y) refl
    ∎)
    y≡z

trans→sym : ∀ {x y z : A} {x≡y : x ≡ y} {y≡z : y ≡ z} {x≡z : x ≡ z}
            → trans x≡y y≡z ≡ x≡z → y≡z ≡ trans (sym x≡y) x≡z
trans→sym {x≡y = x≡y} {y≡z = y≡z} {x≡z = x≡z} t =
  begin
      y≡z
    ≡⟨ sym trans-reflˡ ⟩
      trans refl y≡z
    ≡⟨ cong (λ p → trans p y≡z) (sym trans-symˡ) ⟩
      trans (trans (sym x≡y) x≡y) y≡z
    ≡⟨ sym trans-trans ⟩
      trans (sym x≡y) (trans x≡y y≡z)
    ≡⟨ cong (trans (sym x≡y)) t ⟩
      trans (sym x≡y) x≡z
  ∎

subst : ∀ {x y : A} (P : A → Set ℓ) → x ≡ y → P x → P y
subst P x≡y Px = transport (cong P x≡y) Px

subst2 : ∀ {v w x y : A} (P : A → A → Set ℓ) → v ≡ w → x ≡ y → P v x → P w y
subst2 {w = w} {x = x} P v≡w x≡y Pvx = subst (λ z → P w z) x≡y (subst (λ u → P u x) v≡w Pvx)

subst-refl : ∀ {x : A} (P : A → Set ℓ) (px : P x) → subst P refl px ≡ px
subst-refl P px = transport-refl px

subst-const : ∀ {x y : A} {P : Set ℓ} (x≡y : x ≡ y) {px : P} → subst (λ x → P) x≡y px ≡ px
subst-const {x = x} {P = P} x≡y {px} = J (λ y′ x≡y′ → subst (λ x → P) x≡y′ px ≡ px)
                                         (subst-refl {x = x} (λ x → P) px) x≡y

apd : ∀ {A : Set ℓ} {P : A → Set ℓ′} (f : ∀ (x : A) → P x) {x y : A} (x≡y : x ≡ y)
      → subst P x≡y (f x) ≡ (f y)
apd {P = P} f {x} x≡y = J (λ y′ x≡y′ → subst P x≡y′ (f x) ≡ (f y′)) (transport-refl (f x)) x≡y

cong-∘ : ∀ {ℓ} {A B C : Set ℓ} {x y : A} (x≡y : x ≡ y) (f : A → B) (g : B → C)
         → cong g (cong f x≡y) ≡ cong (g ∘ f) x≡y
cong-∘ x≡y f g = J (λ z x≡z → cong g (cong f x≡z) ≡ cong (λ x → g (f x)) x≡z) refl x≡y

subst-∘ : ∀ {A B : Set ℓ} {x y : A} {P : B → Set ℓ′} {f : A → B} (x≡y : x ≡ y) {p : P (f x)}
          → subst (P ∘ f) x≡y p ≡ subst P (cong f x≡y) p
subst-∘ {x = x} {y} {P} {f} x≡y {p} = J (λ z x≡z →  subst (P ∘ f) x≡z p ≡ subst P (cong f x≡z) p) refl x≡y

subst-app : ∀ {a₁ a₂ b₁ b₂} {A₁ : Set a₁} {A₂ : Set a₂}
              (B₁ : A₁ → Set b₁) {B₂ : A₂ → Set b₂}
              {f : A₂ → A₁} {x₁ x₂ : A₂} {y : B₁ (f x₁)}
              (g : ∀ x → B₁ (f x) → B₂ x) (x₁≡x₂ : x₁ ≡ x₂)
            → subst B₂ x₁≡x₂ (g x₁ y) ≡ g x₂ (subst B₁ (cong f x₁≡x₂) y)
subst-app {A₂ = A₂} B₁ {B₂ = B₂} {f = f} {x₁ = x₁}{x₂ = x₂}{y = y} g x₁≡x₂ =
  J (λ z x₁≡z → subst B₂ x₁≡z (g x₁ y) ≡ g z (subst B₁ (cong f x₁≡z) y))
    (trans (subst-refl B₂ (g x₁ y)) (cong (g x₁) (sym (subst-const (cong{x = x₁} f refl)))))
    x₁≡x₂

-- Equational reasoning for heterogeous equality
module []≡-Reasoning where

  infix  1 []begin_
  infixr 2 _≡[]⟨_⟩_
  infixr 2 _≡⟨_⟩[]_

  []begin_ : ∀ {P : I → Set ℓ} {x : P i0} {y : P i1} → [ P ] x ≡ y → [ P ] x ≡ y
  []begin x≡y = x≡y

  _≡[]⟨_⟩_ : ∀ {P : I → Set ℓ} (x : P i0) {y z : P i1} → [ P ] x ≡ y → y ≡ z → [ P ] x ≡ z
  x ≡[]⟨ x≡y ⟩ y≡z = λ i → hcomp (λ j → λ { (i = i0) → x ; (i = i1) → y≡z j }) (x≡y i)

  _≡⟨_⟩[]_ : ∀ {P : I → Set ℓ} (x : P i0) {y : P i0} {z : P i1} → x ≡ y → [ P ] y ≡ z → [ P ] x ≡ z
  _≡⟨_⟩[]_ {ℓ} {P} x {y} {z} x≡y y≡z = symP {P = λ i → P (~ i)} ([]begin
                                                                  z
                                                                ≡[]⟨ symP y≡z ⟩
                                                                  y
                                                                ≡⟨ sym x≡y ⟩
                                                                  x
                                                                ∎)

open []≡-Reasoning

transport≡→[]≡ : ∀ {ℓ} {A B : Set ℓ} {A≡B : A ≡ B} {p : A} {q : B} → transport A≡B p ≡ q → [ (λ i → A≡B i) ] p ≡ q
transport≡→[]≡ {ℓ} {A} {B} {A≡B} {p} {q} p≡q =
  (J (λ B′ A≡B′ → ∀ (q′ : B′) → transport A≡B′ p ≡ q′ → [ (λ i → A≡B′ i) ] p ≡ q′)
     (λ q′ p≡q′ → begin
                    p
                  ≡⟨ sym (transport-refl p) ⟩
                    transport refl p
                  ≡⟨ p≡q′ ⟩
                    q′
                  ∎)
     A≡B) q p≡q

subst≡→[]≡ : ∀ {P : A → Set ℓ} {x y : A} {p : P x} {q : P y} {x≡y : x ≡ y}
             → subst P x≡y p ≡ q → [ (λ i → P (x≡y i)) ] p ≡ q
subst≡→[]≡ {ℓ} {A} {ℓ′} {P} {x} {y} {p} {q} {x≡y} p≡q =
  (J (λ y′ x≡y′ → ∀ (q′ : P y′)
                  → subst P x≡y′ p ≡ q′ → [ (λ i → P (x≡y′ i)) ] p ≡ q′)
     (λ q′ p≡q′ → begin
                    p
                  ≡⟨ sym (transport-refl p) ⟩
                    transport refl p
                  ≡⟨ cong (λ Px≡Py → transport Px≡Py p)
                          (sym (cong-refl {A = A} {x = x} {f = P})) ⟩
                    transport (cong P refl) p
                  ≡⟨ p≡q′ ⟩
                    q′
                  ∎) x≡y) q p≡q

-- Square in A
[_-_]_≡_ : ∀ {A : Set ℓ} {x y x′ y′ : A} →
           x ≡ x′ → y ≡ y′ → x ≡ y → x′ ≡ y′ → Set ℓ
[ r - s ] p ≡ q = [ (λ i → r i ≡ s i) ] p ≡ q

cong-app-[-]≡ : ∀ {x y x′ y′ : A} (p : x ≡ y) (q : x′ ≡ y′) (r : x ≡ x′) (s : y ≡ y′)
               → [ r - s ] p ≡ q → ∀ (i) → p i ≡ q i
cong-app-[-]≡ p q r s p≡q i = λ j → p≡q j i

-- Function extensionality
→-≡ : ∀ {f g : (x : A) → P x} → (∀ (x : A) → f x ≡ g x) → f ≡ g
→-≡ fx≡gx = λ i x → fx≡gx x i

→-≡′ : ∀ {f g : {x : A} → P x} → (∀ {x : A} → f {x} ≡ g {x}) → (λ {x} → f {x}) ≡ (λ {x} → g {x})
→-≡′ fx≡gx = λ i → fx≡gx i

-- Equality characterization for Σ
Σ-≡ : ∀ {x y : A} {p : P x} {q : P y} →
        Σ (x ≡ y) (λ x≡y → [ (λ i → P (x≡y i)) ] p ≡ q) → _≡_ {A = Σ A P} (x , p) (y , q)
Σ-≡ {ℓ} {A} {P} {x} {y} {p} {q} (x≡y , p≡q) = λ i → (x≡y i) , (p≡q i)

-- Equality characterization for _×_
×-≡ : ∀ {a a′ : A} {b b′ : B} → a ≡ a′ → b ≡ b′ → (a , b) ≡ (a′ , b′)
×-≡ a≡a′ b≡b′ = λ i → (a≡a′ i) , (b≡b′ i)
