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
    incr<  : ∀{m n} → ⦃ m < n ⦄ → suc m < suc n

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

{- Arithmetic -}

n<suc : ∀ {n} → n < suc n
n<suc {zero} = refl<
n<suc {suc n} = incr< ⦃ n<suc ⦄

0<from : ∀ {n k} → n < k → 0 < k
0<from refl< = refl<
0<from (incr< ⦃ _ ⦄) = refl<

mutual
  <-pred : ∀ {m n k} → m < n → n < suc k → m < k
  <-pred refl< (incr< ⦃ q ⦄) = 0<from q
  <-pred (incr< ⦃ p ⦄) (incr< ⦃ q ⦄) = suc<from p q

  suc<from : ∀ {m n k} → m < n → n < k → suc m < k
  suc<from () refl<
  suc<from p (incr< ⦃ q ⦄) = incr< ⦃ <-pred p (incr< ⦃ q ⦄) ⦄

<⊔n-L : ∀{x y z} → x < y → x < (y ⊔n z)
<⊔n-L {x} {suc y} {zero} pf = pf
<⊔n-L {zero} {suc y} {suc z} refl< = refl<
<⊔n-L {suc x} {suc y} {suc z} (incr< ⦃ pf ⦄) = incr< ⦃ <⊔n-L pf ⦄

<⊔n-R : ∀{x y z} → x < y → x < (z ⊔n y)
<⊔n-R {x} {suc y} {zero} pf = pf
<⊔n-R {zero} {suc y} {suc z} refl< = refl<
<⊔n-R {suc x} {suc y} {suc z} (incr< ⦃ pf ⦄) = incr< ⦃ <⊔n-R pf ⦄

<⊔n-suc-L : ∀{x y} → x < (suc x ⊔n y)
<⊔n-suc-L {x} {y} = <⊔n-L {x} {suc x} {y} n<suc

<⊔n-suc-R : ∀{x y} → x < (y ⊔n suc x)
<⊔n-suc-R {x} {y} = <⊔n-R {y = suc x} n<suc
