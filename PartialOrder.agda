{-# OPTIONS --cubical --safe #-}

open import Level using (Level; _⊔_) renaming (suc to ℓ-suc)
open import Data.Unit using (⊤; tt)
open import Data.Nat using (ℕ; zero; suc) renaming (_≤_ to _≤ᴺ_; z≤n to z≤ᴺn; s≤s to s≤ᴺs
                                                   ; _+_ to _+ᴺ_; _⊔_ to _⊔ᴺ_)
open import Data.Nat.Properties using (m≤m⊔n; n≤m⊔n)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂; ∃-syntax)
open import Function using (_∘_; _$_)

open import CubicalIdentity using (_≡_; refl; cong; trans; subst; →-≡; subst≡→[]≡)
open CubicalIdentity.≡-Reasoning
open import Sets

--*
{-
  This module introduces the notion of partial order, monotonous function and increasing and directed sequence.
-
  The partial orders in this module are propositional which implies that the carrier is a set.
-}
--*

module PartialOrder where

private
  variable
    ℓ ℓ′ : Level

-- Partial Order (where ≤ is a Proposition)
record PartialOrder (A : Set ℓ) : Set (ℓ ⊔ (ℓ-suc ℓ′)) where
  infix 4 _≤_

  field
    _≤_ : A → A → Set ℓ′
    ≤-refl : ∀ {x : A} → x ≤ x
    ≤-antisym : ∀ {x y : A} → x ≤ y → y ≤ x → x ≡ y
    ≤-trans : ∀ {x y z : A} → x ≤ y → y ≤ z → x ≤ z
    ≤-prop : ∀ {x y : A} → IsProp (x ≤ y)

  -- The carrier is a set (using Theorem 7.2.2 from the HoTT book)
  A-set : IsSet A
  A-set = A-is-set A (λ x y → x ≤ y × y ≤ x)
                     (λ { (x≤y₁ , y≤x₁) (x≤y₂ , y≤x₂) i → ≤-prop x≤y₁ x≤y₂ i
                                                        , ≤-prop y≤x₁ y≤x₂ i})
                     (≤-refl , ≤-refl) (λ { (x≤y , y≤x) → ≤-antisym x≤y y≤x})

TrivPartialOrder : PartialOrder ⊤
TrivPartialOrder =
  record
    { _≤_ = λ x y → ⊤
    ; ≤-refl = tt
    ; ≤-antisym = λ { {tt} {tt} tt tt → refl }
    ; ≤-trans = λ x y → tt
    ; ≤-prop = λ { tt tt → refl }
    }

ℕ-≤ : PartialOrder ℕ
ℕ-≤ =
  record
    { _≤_ = _≤ᴺ_
    ; ≤-refl = ≤ᴺ-refl
    ; ≤-antisym = ≤ᴺ-antisym
    ; ≤-trans = ≤ᴺ-trans
    ; ≤-prop = ≤ᴺ-prop
    }
  where
    ≤ᴺ-refl : ∀ {n : ℕ} → n ≤ᴺ n
    ≤ᴺ-refl {zero} = z≤ᴺn
    ≤ᴺ-refl {suc n} = s≤ᴺs ≤ᴺ-refl
    ≤ᴺ-antisym : ∀ {m n : ℕ} → m ≤ᴺ n → n ≤ᴺ m → m ≡ n
    ≤ᴺ-antisym z≤ᴺn z≤ᴺn = refl
    ≤ᴺ-antisym (s≤ᴺs m≤ᴺn) (s≤ᴺs n≤ᴺm) = cong suc (≤ᴺ-antisym m≤ᴺn n≤ᴺm)
    ≤ᴺ-trans : ∀ {m n p : ℕ} → m ≤ᴺ n → n ≤ᴺ p → m ≤ᴺ p
    ≤ᴺ-trans z≤ᴺn n≤ᴺp = z≤ᴺn
    ≤ᴺ-trans (s≤ᴺs m≤ᴺn) (s≤ᴺs n≤ᴺp) = s≤ᴺs (≤ᴺ-trans m≤ᴺn n≤ᴺp)
    ≤ᴺ-prop : ∀ {m n : ℕ} (p q : m ≤ᴺ n) → p ≡ q
    ≤ᴺ-prop z≤ᴺn z≤ᴺn = refl
    ≤ᴺ-prop (s≤ᴺs p) (s≤ᴺs q) = cong s≤ᴺs (≤ᴺ-prop p q)

≤ᴺ-natural : ∀ {n m : ℕ} → n ≤ᴺ m → ∃[ k ] (k +ᴺ n ≡ m)
≤ᴺ-natural {zero} {m} z≤ᴺn = m , +ᴺ-zero m
  where
    +ᴺ-zero : ∀ (n : ℕ) → n +ᴺ 0 ≡ n
    +ᴺ-zero zero = refl
    +ᴺ-zero (suc n) = cong suc (+ᴺ-zero n)
≤ᴺ-natural (s≤ᴺs n≤ᴺm) = (proj₁ $ ≤ᴺ-natural n≤ᴺm),
                         (trans (+ᴺ-suc _ _) $ cong suc $ proj₂ $ ≤ᴺ-natural n≤ᴺm)
  where
    +ᴺ-suc : ∀ (n m : ℕ) → n +ᴺ suc m ≡ suc (n +ᴺ m)
    +ᴺ-suc zero m = refl
    +ᴺ-suc (suc n) m = cong suc $ +ᴺ-suc n m

private
  variable
    A B : Set ℓ

module _ (PO : PartialOrder {ℓ} {ℓ′} A) where
  open PartialOrder PO

  -- Partial Order on the function space (X → A)
  →-PO : ∀ {ℓ-X : Level} (X : Set ℓ-X) → PartialOrder (X → A)
  →-PO X = record
             { _≤_ = λ f g → ∀ (x : X) → f x ≤ g x
             ; ≤-refl = λ x → ≤-refl
             ; ≤-antisym = λ fx≤gx gx≤fx → →-≡ (λ x → ≤-antisym (fx≤gx x) (gx≤fx x))
             ; ≤-trans = λ fx≤gx gx≤hx x → ≤-trans (fx≤gx x) (gx≤hx x)
             ; ≤-prop = λ fx≤gx fx≤gx′ → →-≡ (λ x → ≤-prop (fx≤gx x) (fx≤gx′ x))
             }

  Seq = ℕ → A

  -- Increasingness
  Inc : Seq → Set ℓ′
  Inc seq = ∀ (n : ℕ) → seq n ≤ seq (suc n)

  -- Intensional Directedness (non-truncated)
  Dir : Seq → Set ℓ′
  Dir seq = ∀ (n m : ℕ) → ∃[ k ] ((seq n ≤ seq k) × (seq m ≤ seq k)) 

  -- Extensional Directedness (truncated)
  ‖Dir‖ : Seq → Set ℓ′
  ‖Dir‖ seq = ∀ (n m : ℕ) → ‖ ∃[ k ] ((seq n ≤ seq k) × (seq m ≤ seq k)) ‖

  Is-ub : Seq → A → Set ℓ′
  Is-ub s ub = ∀ n → s n ≤ ub

  Is-lub : Seq → A → Set (ℓ ⊔ ℓ′)
  Is-lub s ub = ∀ {b} → (∀ n → s n ≤ b) → ub ≤ b

  record Lub (s : Seq) : Set (ℓ ⊔ ℓ′) where
    field
      ub : A
      is-ub : Is-ub s ub
      is-l  : Is-lub s ub

  open Lub

  Lub→Σ : ∀ {s : Seq} → Lub s → Σ A (λ ub → Is-ub s ub × Is-lub s ub)
  Lub→Σ l = ub l , is-ub l , is-l l

  Lub←Σ : ∀ {s : Seq} → Σ A (λ ub → Is-ub s ub × Is-lub s ub) → Lub s
  Lub←Σ (ub-l , is-ub-l , is-l-l) = record
                                      { ub = ub-l
                                      ; is-ub = is-ub-l
                                      ; is-l = is-l-l }

  Lub→Σ-≡ : ∀ {s : Seq} (l l′ : Lub s) → (Lub→Σ l ≡ Lub→Σ l′) → l ≡ l′
  Lub→Σ-≡ l l′ l≡l′ = λ i → record
                              { ub = proj₁ (l≡l′ i)
                              ; is-ub = proj₁ (proj₂ (l≡l′ i))
                              ; is-l = proj₂ (proj₂ (l≡l′ i))
                              }

  Lub-≡ : ∀ {s : Seq} {l l′ : Lub s} → ub l ≡ ub l′ → l ≡ l′
  Lub-≡ {s} {l} {l′} ub≡ub′ = Lub→Σ-≡ l l′ (Σ-Prop-≡ (IsProp-× (IsProp-∀ (λ _ → ≤-prop))
                                                                (IsProp-∀′ (IsProp-∀ (λ _ → ≤-prop))))
                                                      ub≡ub′)

  -- Lubs are unique
  Lub-prop : ∀ (s : Seq) → IsProp (Lub s)
  Lub-prop s l l′ = Lub-≡ (≤-antisym (is-l l (is-ub l′))
                                     (is-l l′ (is-ub l)))

  Cofinal : ∀ (s s′ : Seq) → Set ℓ′
  Cofinal s s′ = ∀ n → ∃[ m ] (s n ≤ s′ m)

  cofinal-lubs : ∀ (s s′ : Seq) → Cofinal s s′ → (b : Lub s) → (c : Lub s′) → ub b ≤ ub c
  cofinal-lubs s s′ cof b c = is-l b (λ n → ≤-trans (proj₂ $ cof n) (is-ub c $ proj₁ $ cof n))

  ‖Cofinal‖ : ∀ (s s′ : Seq) → Set ℓ′
  ‖Cofinal‖ s s′ = ∀ n → ‖ ∃[ m ] (s n ≤ s′ m) ‖

  ‖cofinal-lubs‖ : ∀ (s s′ : Seq) → ‖Cofinal‖ s s′ → (b : Lub s) → (c : Lub s′) → ub b ≤ ub c
  ‖cofinal-lubs‖ s s′ cof b c = is-l b (λ n → ‖‖-Rec ≤-prop (λ (m , sn≤s′m) → ≤-trans sn≤s′m (is-ub c m)) (cof n))

  module _ (PO′ : PartialOrder {ℓ}{ℓ′} B) where

    open PartialOrder PO′ renaming (_≤_ to _≤′_)

    Mono : (A → B) → Set _
    Mono f = ∀ {x y : A} → x ≤ y → f x ≤′ f y

    -- Monotonous Function
    record MonoFun : Set (ℓ ⊔ ℓ′) where
      constructor _↑_
     
      field
        fun : A → B
        mono : Mono fun

    infix 4 _↑_

  -- Increasing Sequence
  record IncSeq : Set (ℓ ⊔ ℓ′) where
    constructor _↗_
    field
      seq : ℕ → A
      inc : Inc seq

  infix 4 _↗_

  -- Directed Sequence
  record DirSeq : Set (ℓ ⊔ ℓ′) where
    constructor _⇗_
    field
      seq : ℕ → A
      dir : Dir seq

  infix 4 _⇗_

  -- Directed Sequence
  record ‖DirSeq‖ : Set (ℓ ⊔ ℓ′) where
    constructor _‖⇗‖_
    field
      seq : ℕ → A
      dir : ‖Dir‖ seq

  infix 4 _‖⇗‖_

module _ {PO : PartialOrder {ℓ} {ℓ′} A} where
  open PartialOrder PO

  -- Applying an increasing sequence to its argument
  _[_] : IncSeq {A = A} PO → ℕ → A
  (seq ↗ inc) [ n ] = seq n

  -- Applying a directed sequence to its argument
  _⟨_⟩ : DirSeq {A = A} PO → ℕ → A
  (seq ⇗ dir) ⟨ n ⟩ = seq n
  
  _⟪_⟫ : ‖DirSeq‖ {A = A} PO → ℕ → A
  (seq ‖⇗‖ dir) ⟪ n ⟫ = seq n

  -- Equality characterization for increasing sequences
  IncSeq-≡ : ∀ {s t : ℕ → A} {incₛ : Inc PO s} {incₜ : Inc PO t}
             → (s ≡ t) → _≡_ {A = IncSeq {A = A} PO} (s ↗ incₛ) (t ↗ incₜ)
  IncSeq-≡ {s} {t} {incₛ} {incₜ} s≡t = λ i → s≡t i
                                             ↗ subst≡→[]≡ {P = Inc PO} {p = incₛ} {q = incₜ} {x≡y = s≡t}
                                                          (→-≡ (λ _ → ≤-prop _ _)) i

  -- Equality characterization for truncated directed sequences
  ‖DirSeq‖-≡ : ∀ {s t : ℕ → A} {dirₛ : ‖Dir‖ PO s} {dirₜ : ‖Dir‖ PO t}
               → (s ≡ t) → _≡_ {A = ‖DirSeq‖ {A = A} PO} (s ‖⇗‖ dirₛ) (t ‖⇗‖ dirₜ)
  ‖DirSeq‖-≡ {s} {t} {dirₛ} {dirₜ} s≡t = λ i → s≡t i
                                               ‖⇗‖ subst≡→[]≡ {P = ‖Dir‖ PO} {p = dirₛ} {q = dirₜ} {x≡y = s≡t}
                                                              (→-≡ (λ _ → →-≡ (λ _ → ‖‖-prop _ _))) i

  Dir-→ : ∀ {s t : ℕ → A} (dir : Dir PO s) → (s ≡ t) → Dir PO t
  Dir-→ dir s≡t = subst (Dir PO) s≡t dir

  IncSeq-mono : ∀ (s : IncSeq PO) (n m : ℕ) → s [ n ] ≤ s [ m +ᴺ n ]
  IncSeq-mono (seq ↗ inc) n zero = ≤-refl
  IncSeq-mono (seq ↗ inc) n (suc m) = ≤-trans (IncSeq-mono (seq ↗ inc) n m) (inc (m +ᴺ n))

  IncSeq-trans : ∀ (s : IncSeq PO) (n m : ℕ) → n ≤ᴺ m → s [ n ] ≤ s [ m ]
  IncSeq-trans s n m n≤ᴺm = subst (λ m → (s [ n ]) ≤ (s [ m ]))
                                  (proj₂ (≤ᴺ-natural n≤ᴺm))
                                  (IncSeq-mono s _ _)

  IncSeq→DirSeq : IncSeq PO → DirSeq PO
  IncSeq→DirSeq (seq ↗ inc) = seq ⇗ λ m n → (n ⊔ᴺ m) 
                                            , IncSeq-trans (seq ↗ inc) m (n ⊔ᴺ m) (n≤m⊔n n m)
                                            , IncSeq-trans (seq ↗ inc) n (n ⊔ᴺ m) (m≤m⊔n n m)

  -- this of little help because there are many constant
  -- sequences with different directedness proofs
  DirSeq-const : A → DirSeq PO
  DirSeq-const x = (λ _ → x) ⇗ (λ n m → n ⊔ᴺ m , (≤-refl , ≤-refl))

  ‖DirSeq‖-const : A → ‖DirSeq‖ PO
  ‖DirSeq‖-const x = (λ _ → x) ‖⇗‖ (λ n m → ∣ n ⊔ᴺ m , (≤-refl , ≤-refl) ∣)

  module _ {PO′ : PartialOrder {ℓ} {ℓ′} B} where 
    DirSeq-mono : DirSeq PO → MonoFun PO PO′ → DirSeq PO′
    DirSeq-mono (seq ⇗ dir) (fun ↑ mono) = fun ∘ seq ⇗ λ n m → (proj₁ (dir n m)) , (mono (proj₁ (proj₂ (dir n m)))
                                                                               , (mono (proj₂ (proj₂ (dir n m)))))
  
    ‖DirSeq‖-mono : ‖DirSeq‖ PO → MonoFun PO PO′ → ‖DirSeq‖ PO′
    ‖DirSeq‖-mono (seq ‖⇗‖ dir) (fun ↑ mono) = (fun ∘ seq)
                                             ‖⇗‖ (λ n m → ‖‖-Rec ‖‖-prop
                                                                 (λ { (k , sn≤sk , sm≤sk)
                                                                  → ∣ k , mono sn≤sk , mono sm≤sk ∣ })
                                                                 (dir n m))
