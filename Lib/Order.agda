module Lib.Order where

open import Agda.Primitive
open import Lib.Basic

infixl 10 _≤_
data _≤_ : ℕ → ℕ → Set where
  instance
    refl≤ : ∀{n} → n ≤ n
    incr≤  : ∀{m n} → ⦃ m ≤ n ⦄ → m ≤ suc n

infixl 10 _<_
data _<_ : ℕ → ℕ → Set where
  instance
    refl< : ∀{n} → 0 < suc n
    incr<  : ∀{m n} → ⦃ m < n ⦄ → m < suc n

{- Sum types -}
data Or {ℓ ℓ'} (A : Set ℓ) (B : Set ℓ') : Set (ℓ ⊔ ℓ') where
    inl : A → Or A B
    inr : B → Or A B

{- Properties -}
zero≤ : ∀{n} → 0 ≤ n
zero≤ {zero} = refl≤
zero≤ {suc n} = incr≤ ⦃ zero≤ ⦄

suc≤ : ∀{m n} → ⦃ m ≤ n ⦄ → suc m ≤ suc n
suc≤ ⦃ refl≤ ⦄ = refl≤
suc≤ ⦃ incr≤ ⦄ = incr≤ ⦃ suc≤ ⦄

{- Least upper bounds -}

infixl 8 _⊔n_
_⊔n_ : ℕ → ℕ → ℕ
zero ⊔n y = y
(suc x) ⊔n zero = suc x
(suc x) ⊔n (suc y) = suc (x ⊔n y)

≤⊔n-L : ∀{m n} → m ≤ (m ⊔n n)
≤⊔n-L {zero} {n} = zero≤
≤⊔n-L {suc m} {zero} = refl≤
≤⊔n-L {suc m} {suc n} = suc≤ ⦃ ≤⊔n-L ⦄

≤⊔n-R : ∀{m n} → n ≤ (m ⊔n n)
≤⊔n-R {zero} {n} = refl≤
≤⊔n-R {suc m} {zero} = zero≤
≤⊔n-R {suc m} {suc n} = suc≤ ⦃ ≤⊔n-R ⦄

-- Dichotomy
⊔n-dicho : ∀{m n} → Or (m ⊔n n ≡ m) (m ⊔n n ≡ n)
⊔n-dicho {zero} {n} = inr refl
⊔n-dicho {suc m} {zero} = inl refl
⊔n-dicho {suc m} {suc n} with ⊔n-dicho {m} {n}
... | inl p rewrite p = inl refl
... | inr p rewrite p = inr refl

toFin : ∀{m n} → m < n → Fin n
toFin refl< = zero
toFin (incr< ⦃ pf ⦄) = suc (toFin pf)

try : (⦃ 0 ≤ 1 ⦄ → Set) → Set
try A = A
