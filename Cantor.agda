{-# OPTIONS --cubical --safe #-}

open import Level using (Level; _⊔_) renaming (suc to ℓ-suc)

open import Data.Nat hiding (_⊔_)
open import Data.Nat.Properties
open import Data.Product
open import Relation.Binary.PropositionalEquality
open import Function
open import Data.Empty using (⊥-elim)
open import Data.Sum as Sum using (_⊎_; inj₁; inj₂; [_,_])

-- Cantor pairing function
-- π sn m = (sn + m)(sn + m + 1)/2 + m
-- = π n m + ((n + m + 1) + (n + m) + 1)/2 
-- = π n m + n + s m 
-- 
-- π 0 sm = sm (sm + 1)/2 + sm
-- π 0 m + (m + 1 + m + 1)/2 + 1
-- = π 0 m + m + 2

π : ℕ → ℕ → ℕ
π 0 0 = 0
π 0 (suc m) = π 0 m + suc m + 1
π (suc n) m = π n m + suc (n + m)

-- inverses
π₂⁻¹ π₁⁻¹ : ℕ → ℕ

π₂⁻¹ 0 = 0
π₂⁻¹ (suc n) with (π₁⁻¹ n)
π₂⁻¹ (suc n) | zero  = 0
π₂⁻¹ (suc n) | suc _ = suc (π₂⁻¹ n) 

π₁⁻¹ 0 = 0
π₁⁻¹ (suc n) with (π₁⁻¹ n)
π₁⁻¹ (suc n) | zero = suc (π₂⁻¹ n)
π₁⁻¹ (suc n) | suc m = m

π-prop : ∀ (n m : ℕ) → π n (suc m) ≡ suc (π (suc n) m)
π-prop zero m rewrite +-suc (π 0 m) m | +-assoc (π 0 m) m 1
  | +-comm m 1 | +-suc (π 0 m) m = refl 
π-prop (suc n) m rewrite π-prop n m rewrite +-suc n m = refl 

π-prop* : ∀ (n m : ℕ) → π n m ≡ π (n + m) 0 + m
π-prop* n zero rewrite +-identityʳ n | +-identityʳ (π n 0) = refl
π-prop* n (suc m) rewrite π-prop n m | π-prop* n m | +-suc n m
  | +-identityʳ (n  + m) | +-suc (π (n + m) 0 + suc (n + m)) m
  | +-assoc (π (n + m) 0)  (suc (n + m)) m
  | +-assoc (π (n + m) 0) m (suc (n + m))
  | +-comm m (suc (n + m)) = refl

π′ : ℕ → ℕ
π′ 0 = 0
π′ (suc n) = π′ n + (suc n)

π′≡π-0 : ∀ (n : ℕ) → π′ n ≡ π n 0
π′≡π-0 zero = refl
π′≡π-0 (suc n) rewrite +-identityʳ n | π′≡π-0 n = refl

-- well-foundedness of an order
data ↓ {ℓ ℓ'} {A : Set ℓ} (_>_ : A → A → Set ℓ') : A → Set (ℓ ⊔ ℓ') where
  pf↓ : ∀ {x : A} → (∀ {y : A} → x > y → ↓ _>_ y) → ↓ _>_ x

-- well-foundedness of natural number comparison
↓-> : ∀ (x : ℕ) → ↓ _>_ x
↓-> x = pf↓ (h x)
  where h : ∀ x → ∀ {y} → x > y → ↓ _>_ y
        h (suc x) {y} p with m≤n⇒m<n∨m≡n p 
        h (suc x) {y} p | inj₁ u = h x (≤-pred u)
        h (suc x) {y} p | inj₂ u rewrite (suc-injective u) = ↓-> x

-- well-foundedness of a lexicographic combination of two well-founded orders
module lexcomb {ℓ ℓ' ℓ₁ ℓ₂}{A : Set ℓ}{B : Set ℓ'}(_>A_ : A → A → Set ℓ₁)(_>B_ : B → B → Set ℓ₂) where
  
  _>lex_ : A × B → A × B → Set (ℓ ⊔ ℓ₁ ⊔ ℓ₂)
  (a , b) >lex (a' , b') = a >A a' ⊎ (a ≡ a' × b >B b')

  ↓-lex : {a : A} → ↓ _>A_ a → ((b : B) → ↓ _>B_ b) → {b : B} → ↓ _>lex_ (a , b)
  ↓-lex {a} (pf↓ fA) tB {b} = pf↓ (helper fA (tB b))
     where helper : {a : A} → (∀{y : A} → a >A y → ↓ _>A_ y) → {b : B} → ↓ _>B_ b → {y : A × B} → (a , b) >lex y → ↓ _>lex_ y
           helper fA _ {a' , b'} (inj₁ u) = ↓-lex (fA u) tB
           helper fA (pf↓ fB) {a' , b'} (inj₂ (u , u')) rewrite u = pf↓ (helper fA (fB u'))

open lexcomb (_>_) (_>_)

data Lex (n m : ℕ) : Set where
  lex : (∀ k m′ → k < n → Lex k m′) → (∀ k → k < m → Lex n k) → Lex n m

-- recursive calls are lexicographic, like in the Ackermann function,
-- but Agda cannot natively detect termination for some reason
h₁ : ∀ (n k : ℕ) → (↓ _>lex_ (n , k)) → (k ≤ n) → π₁⁻¹ (π′ n + k) ≡ n ∸ k
h₂ : ∀ (n k : ℕ) → (↓ _>lex_ (n , k)) → (k ≤ n) → π₂⁻¹ (π′ n + k) ≡ k

h₁ zero k (pf↓ t) k≤0 rewrite n≤0⇒n≡0 k≤0 = refl
h₁ (suc n) zero (pf↓ t) _
  rewrite +-identityʳ (π′ n + suc n)
    | +-suc (π′ n) n
    | h₁ n n (t (inj₁ ≤-refl)) ≤-refl
    | n∸n≡0 n
  = cong suc (h₂ n n (t (inj₁ ≤-refl)) ≤-refl)
  
h₁ (suc n) (suc k) (pf↓ t) sk≤sn
  rewrite +-suc (π′ n + suc n) k
    | h₁ (suc n) k (t $ inj₂ (refl , ≤-refl)) (≤-trans (n≤1+n k) sk≤sn)
  with (suc n ∸ k) | inspect (suc n ∸_) k 
... | 0     | [ eq ] = ⊥-elim (1+n≰n (≤-trans (m∸n≡0⇒m≤n{suc n}{k} eq) $ ≤-pred $ sk≤sn))
... | suc m | [ eq ] = suc-injective (trans (sym eq) $ +-∸-assoc 1 sk≤sn) 

h₂ zero k (pf↓ t) k≤0 rewrite n≤0⇒n≡0 k≤0 = refl
h₂ (suc n) zero  (pf↓ t) _
  rewrite +-identityʳ (π′ n + suc n)
    | +-suc (π′ n) n
    | h₁ n n (t $ inj₁  ≤-refl) ≤-refl
    | n∸n≡0 n = refl
h₂ (suc n) (suc k)  (pf↓ t) sk≤sn
  rewrite +-suc (π′ n + suc n) k
    | h₁ (suc n) k (t $ inj₂ (refl , ≤-refl)) (≤-trans (n≤1+n k) sk≤sn)
  with (suc n ∸ k) | inspect (suc n ∸_) k 
... | 0     | [ eq ] = ⊥-elim $ 1+n≰n (≤-trans (m∸n≡0⇒m≤n{suc n}{k} eq) $ ≤-pred $ sk≤sn)
  where h = ≤-trans (m∸n≡0⇒m≤n{suc n}{k} eq) $ ≤-pred sk≤sn
... | suc m | [ eq ] = cong suc (h₂ (suc n) k (t (inj₂ (refl , ≤-refl))) (≤-trans (n≤1+n k) sk≤sn))

π₁⁻¹-0 : ∀ (n : ℕ) → π₁⁻¹ (π n 0) ≡ n
π₁⁻¹-0 n rewrite (sym (π′≡π-0 n)) | sym (+-identityʳ (π′ n)) = h₁ n 0 (↓-lex (↓-> n) ↓-> ) z≤n

π₂⁻¹-0 : ∀ (n : ℕ) → π₂⁻¹ (π n 0) ≡ 0
π₂⁻¹-0 n rewrite (sym (π′≡π-0 n)) | sym (+-identityʳ (π′ n))  = h₂ n 0 (↓-lex (↓-> n)  ↓->) z≤n

π-surj' : ∀ (n : ℕ) → π (π₁⁻¹ n + π₂⁻¹ n) 0 + π₂⁻¹ n ≡ n
π-surj' zero = refl
π-surj' (suc n) with π₁⁻¹ n | inspect π₁⁻¹ n
π-surj' (suc n) | zero  | [ eq ] rewrite +-identityʳ (π₂⁻¹ n)
  | +-identityʳ (π₂⁻¹ n) | +-identityʳ (π (π₂⁻¹ n) 0 + suc (π₂⁻¹ n))
  | +-suc (π (π₂⁻¹ n) 0) (π₂⁻¹ n)
  = cong suc (trans (cong (_+ π₂⁻¹ n) h) (π-surj' n))
  where
    h : π (π₂⁻¹ n) 0 ≡ π (π₁⁻¹ n + π₂⁻¹ n) 0 
    h rewrite eq = refl 

π-surj' (suc n) | suc m | [ eq ] rewrite +-suc (π (m + suc (π₂⁻¹ n)) 0) (π₂⁻¹ n)
  = trans (cong (λ w → suc (π w 0 + π₂⁻¹ n)) h) (cong suc (π-surj' n)) 
    where
      h : m + suc (π₂⁻¹ n) ≡ π₁⁻¹ n + π₂⁻¹ n
      h = trans (+-suc m (π₂⁻¹ n)) (cong (_+ π₂⁻¹ n) (sym eq)) 

π-surj : ∀ (n : ℕ) → π (π₁⁻¹ n) (π₂⁻¹ n) ≡ n
π-surj n = trans (π-prop* (π₁⁻¹ n) (π₂⁻¹ n)) (π-surj' n) 

π₁⁻¹π : ∀ {n m : ℕ} → π₁⁻¹ (π n m) ≡ n
π₂⁻¹π : ∀ {n m : ℕ} → π₂⁻¹ (π n m) ≡ m

π₁⁻¹π {zero} {zero} = refl
π₁⁻¹π {suc n} {zero} = π₁⁻¹-0 (suc n)
π₁⁻¹π {n}{suc m} rewrite π-prop n m | π₁⁻¹π {suc n}{m} = refl

π₂⁻¹π {zero} {zero} = refl
π₂⁻¹π {suc n} {zero} = π₂⁻¹-0 (suc n)
π₂⁻¹π {n} {suc m} rewrite π-prop n m | π₁⁻¹π {suc n} {m} | π₂⁻¹π {suc n} {m} = refl

