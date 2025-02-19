module Lib.Basic where

open import Agda.Primitive

infix 4 _≡_
infixl 5 _,_
infixl 3 _×_

{- Propositional equality -}

data _≡_ {ℓ} {A : Set ℓ} (x : A) : A → Set ℓ where
  instance refl : x ≡ x
{-# BUILTIN EQUALITY _≡_ #-}

{- Type conversion -}
conv : ∀{ℓ} {A B : Set ℓ} → A ≡ B → A → B
conv refl a = a

{- Congruence -}
cong : ∀{ℓ ℓ'} {A : Set ℓ} {B : Set ℓ'} (f : A → B){a₀ a₁ : A} (a₂ : a₀ ≡ a₁)
    → f a₀ ≡ f a₁
cong f refl = refl

{- Leibniz rule -}
subst : ∀{ℓ ℓ'} {A : Set ℓ} (P : A → Set ℓ'){x y : A} (p : x ≡ y) → P x → P y
subst P refl a = a

{- Type transport -}
coerce : ∀{ℓ} {A B : Set ℓ}(p : A ≡ B) → A → B
coerce refl a = a

{- Transitive -}
tran : ∀{ℓ} {A : Set ℓ} {x y z : A} → x ≡ y → y ≡ z → x ≡ z
tran refl refl = refl 

{- Symmetric -}
sym : ∀{ℓ} {A : Set ℓ} {x y : A} → x ≡ y → y ≡ x
sym refl = refl

{- J rule -}
J : ∀{ℓ ℓ'} {A : Set ℓ} {x : A} (P : {y : A} → x ≡ y → Set ℓ') → P refl → {y : A} → (w : x ≡ y) → P w
J P pr refl = pr

----------------------------------------------

{- True and false -}
record ⊤ : Set where

tt : ⊤
tt = record {}

data ⊥ : Set where

{- Contradiction -}
absurd : ∀{ℓ} {C : Set ℓ} → ⊥ → C
absurd ()

----------------------------------------------

{- Commonly used datatypes -}

{- Dependent pair -}
record Σ {ℓ ℓ'} (A : Set ℓ) (B : A → Set ℓ') : Set (ℓ ⊔ ℓ') where
  constructor _,_
  field
    fst : A
    snd : B fst
open Σ public

_×_ : ∀{ℓ ℓ'} → Set ℓ → Set ℓ' → Set (ℓ ⊔ ℓ')
A × B = Σ A λ _ → B

{- Boolean -}
data Bool : Set where
  true false : Bool

if : ∀{ℓ}(P : Bool → Set ℓ) → P true → P false → (b : Bool) → P b
if P u v true  = u
if P u v false = v

_∨_ : Bool → Bool → Bool
true ∨ _ = true
false ∨ true = true
false ∨ false = false

_∧_ : Bool → Bool → Bool
true ∧ true = true
true ∧ false = false
false ∧ _ = false

¬ : Bool → Bool
¬ true = false
¬ false = true

{- Natural numbers -}
data ℕ : Set where
  zero : ℕ
  suc  : ℕ → ℕ
{-# BUILTIN NATURAL ℕ #-}

infixl 5 _+_
_+_ : ℕ → ℕ → ℕ
zero + y = y
(suc x) + y = suc (x + y)

infixl 7 _*_
_*_ : ℕ → ℕ → ℕ
zero * y = zero
(suc _) * zero = zero
(suc x) * (suc y) = (suc y) + (x * (suc y))

infixl 8 _⊔n_
_⊔n_ : ℕ → ℕ → ℕ
zero ⊔n y = y
(suc x) ⊔n zero = suc x
(suc x) ⊔n (suc y) = suc (x ⊔n y)

infixl 10 _≤_
data _≤_ : ℕ → ℕ → Set where
  refl : ∀{n} → n ≤ n
  sucP  : ∀{m n} → m ≤ n → suc m ≤ suc n

iterN : ∀{i}(C : ℕ → Set i) → C zero → (∀{n} → C n → C (suc n)) → (n : ℕ) → C n
iterN C z s zero = z
iterN C z s (suc n) = s (iterN C z s n)

{- Fin -}
data Fin : ℕ → Set where
  zero : ∀{n} → Fin (suc n)
  suc  : ∀{n} → Fin n → Fin (suc n)

{- Vector -}
data Vec (X : Set) : ℕ → Set where
  <> : Vec X zero
  _,_ : {n : ℕ} → X → Vec X n → Vec X (suc n)

record Lift {ℓ ℓ'} (A : Set ℓ) : Set (ℓ ⊔ ℓ') where
  constructor lift
  field
    unlift : A
open Lift public

----------------------------------------------

{- Commonly used functions -}

id : ∀{ℓ} {A : Set ℓ} → A → A
id x = x

infixr 5 _∘_
_∘_ : ∀{ℓ ℓ' ℓ''} {A : Set ℓ} {B : A → Set ℓ'} {C : (a : A) → B a → Set ℓ''} →
        (f : {a : A}(b : B a) → C a b) →
        (g : (a : A) → B a) →
        (a : A) → C a (g a)
(g ∘ f) x = g (f x)

_$_ : ∀{ℓ ℓ'} {A : Set ℓ} {B : A → Set ℓ'} → 
        (f : (x : A) → B x) → (x : A) → B x
f $ x = f x

_+'_ : ℕ → ℕ → ℕ
a +' b = iterN (λ x → ℕ) b (λ x → suc x) a

ext-⊤ : ∀{i}{A : Set i}{f g : ⊤ → A} → ({t : ⊤} → f t ≡ g t) → f ≡ g
ext-⊤ pf = cong (λ a _ → a) pf

cong-app : ∀{i j}{A : Set i}{B : A → Set j}{f g : (a : A) → B a} → 
  (f ≡ g) → {a : A} → f a ≡ g a
cong-app refl = refl

eee : ∀{x y} → x + y ≡ x +' y
eee {zero} {y} = refl
eee {suc x} {y} = cong suc (eee {x} {y})
