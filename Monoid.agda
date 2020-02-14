{-# OPTIONS --cubical --safe #-}

open import Level using (Level; _⊔_) renaming (suc to ℓ-suc)
open import CubicalIdentity using (_≡_; refl; sym; cong; trans; subst2)
open CubicalIdentity.≡-Reasoning
open import Data.Unit using (⊤; tt)
open import Data.Nat using (ℕ; zero; suc) renaming (_+_ to _+ᴺ_; _≤_ to _≤ᴺ_)
open import Data.Product using (_×_; _,_)

open import PartialOrder

--*
{-
  This module introduces the notion of monoid and ordered monoid. 
-}
--*

module Monoid where

private
  variable
    ℓ ℓ′ : Level

record Monoid : Set (ℓ-suc ℓ) where
  infix 6 _+_
  
  field
    𝕄 : Set ℓ
    _+_ : 𝕄 → 𝕄 → 𝕄
    𝟘 : 𝕄
    +-assoc : ∀ {a b c : 𝕄} → a + (b + c) ≡ (a + b) + c
    +-identityˡ : ∀ {a : 𝕄} → 𝟘 + a ≡ a
    +-identityʳ : ∀ {a : 𝕄} → a + 𝟘 ≡ a

-- The trivial monoid
TrivMonoid : Monoid
TrivMonoid =
  record
    { 𝕄 = ⊤
    ; _+_ = λ x y → tt
    ; 𝟘 = tt
    ; +-assoc = refl
    ; +-identityˡ = λ { {tt} → refl }
    ; +-identityʳ = λ { {tt} → refl }
    }

ℕ-Monoid : Monoid
ℕ-Monoid =
  record
    { 𝕄 = ℕ
    ; _+_ = _+ᴺ_
    ; 𝟘 = zero
    ; +-assoc = λ {m} {n} {p} → +ᴺ-assoc m n p
    ; +-identityˡ = refl
    ; +-identityʳ = λ {n} → +ᴺ-identityʳ n
    }
  where
    +ᴺ-assoc : ∀ (m n p : ℕ) → m +ᴺ (n +ᴺ p) ≡ (m +ᴺ n) +ᴺ p
    +ᴺ-assoc zero n p = refl
    +ᴺ-assoc (suc m) n p = cong suc (+ᴺ-assoc m n p)
    +ᴺ-identityʳ : ∀ (n : ℕ) → n +ᴺ zero ≡ n
    +ᴺ-identityʳ zero = refl
    +ᴺ-identityʳ (suc n) = cong suc (+ᴺ-identityʳ n)

-- Ordered Monoid
record O-Monoid (M : Monoid {ℓ}) : Set (ℓ ⊔ (ℓ-suc ℓ′)) where
  open Monoid M public
  
  field
    PO : PartialOrder.PartialOrder {ℓ} {ℓ′} 𝕄

  open PartialOrder.PartialOrder PO public

  field
    +-monoʳ-≤ : ∀ {a b c : 𝕄} → b ≤ c → a + b ≤ a + c
    𝟘≤a : ∀ {a : 𝕄} → 𝟘 ≤ a

  a+b≡𝟘→a≡𝟘×b≡𝟘 : ∀ {a b : 𝕄} → a + b ≡ 𝟘 → a ≡ 𝟘 × b ≡ 𝟘
  a+b≡𝟘→a≡𝟘×b≡𝟘 {a} {b} a+b≡𝟘 = a≡𝟘 , (begin
                                         b
                                       ≡⟨ sym +-identityˡ ⟩
                                         𝟘 + b
                                       ≡⟨ cong (_+ b) (sym a≡𝟘) ⟩
                                         a + b
                                       ≡⟨ a+b≡𝟘 ⟩
                                         𝟘
                                       ∎)
    where
      a≡𝟘 : a ≡ 𝟘
      a≡𝟘 = ≤-antisym (subst2 (λ x y → x ≤ y)
                              +-identityʳ
                              a+b≡𝟘
                              (+-monoʳ-≤ 𝟘≤a))
                      𝟘≤a

-- The trivial ordered monoid
TrivOMonoid : O-Monoid TrivMonoid
TrivOMonoid =
  record
    { PO = TrivPartialOrder
    ; +-monoʳ-≤ = λ x → tt
    ; 𝟘≤a = tt
    }

ℕ-OMonoid : O-Monoid ℕ-Monoid
ℕ-OMonoid =
  record
    { PO = ℕ-≤
    ; +-monoʳ-≤ = +ᴺ-monoʳ-≤ᴺ
    ; 𝟘≤a = z≤n
    }
  where
    open _≤ᴺ_
    +ᴺ-monoʳ-≤ᴺ : ∀ {m n p : ℕ} → n ≤ᴺ p → m +ᴺ n ≤ᴺ m +ᴺ p
    +ᴺ-monoʳ-≤ᴺ {zero} n≤ᴺp = n≤ᴺp
    +ᴺ-monoʳ-≤ᴺ {suc m} n≤ᴺp = s≤s (+ᴺ-monoʳ-≤ᴺ n≤ᴺp)
