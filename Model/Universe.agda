module Model.Universe where

open import Lib.Basic

infixl 6 _~,_
infixl 7 _~$_

record Universe : Set₁ where
  constructor uni
  field
    Codes : Set
    Meaning : Codes → Set

mutual
  data Code (U : Universe) : Set where
    `N `B `⊤ `⊥ : Code U
    `Π `Σ : (A : Code U) → (⟦ U ~~ A ⟧ → Code U) → Code U
    `Id : (A : Code U) → ⟦ U ~~ A ⟧ → ⟦ U ~~ A ⟧ → Code U
    `U : Code U
    `↑ : Universe.Codes U → Code U

  ⟦_~~_⟧ : (U : Universe) → Code U → Set
  ⟦ U ~~ `N ⟧ = ℕ
  ⟦ U ~~ `B ⟧ = Bool
  ⟦ U ~~ `⊤ ⟧ = ⊤
  ⟦ U ~~ `⊥ ⟧ = ⊥
  ⟦ U ~~ `Π A B ⟧ = (a : ⟦ U ~~ A ⟧) → ⟦ U ~~ B a ⟧
  ⟦ U ~~ `Σ A B ⟧ = Σ ⟦ U ~~ A ⟧ (λ a → ⟦ U ~~ B a ⟧)
  ⟦ U ~~ `Id A x y ⟧ = x ≡ y
  ⟦ U ~~ `U ⟧ = Universe.Codes U
  ⟦ U ~~ `↑ A ⟧ = Universe.Meaning U A

Code₀ : Universe
Code₀ = uni ⊥ (λ ())

mutual
  Type : ℕ → Set
  Type zero = ⊥
  Type (suc n) = Code (uni (Type n) ⟦_⟧)

  ⟦_⟧ : {n : ℕ} → Type n → Set
  ⟦_⟧ {n = suc n} A = ⟦ (uni (Type n) ⟦_⟧) ~~ A ⟧

{- 
  Custom encoding of functions and pairs, 
  so that the shallow embedding could infer more 
  implicit variables.

  Before:
    Tm Γ A = (γ : Γ) → ⟦ A γ ⟧
    ==> A is consumed in ⟦_⟧, so can't imply it in many cases
  
  After:
    Tm Γ A = ~Π Γ A
    ==> A is kept intact, access the underlying function 
        via pattern matching
-}

record ~Π {n : ℕ} (A : Set) (B : A → Type n) : Set where
  constructor ~λ
  field
    ~fun : ((a : A) → ⟦ B a ⟧)

_~$_ : ∀{n A}{B : A → Type n} → ~Π A B → (a : A) → ⟦ B a ⟧
(~λ f) ~$ a = f a

inj₁ : ∀{U}{A A' : Code U}{B : ⟦ U ~~ A ⟧ → Code U}{B' : ⟦ U ~~ A' ⟧ → Code U} →
  `Π A B ≡ `Π A' B' → A ≡ A'
inj₁ refl = refl

inj₂ : ∀{U}{A A' : Code U}{B : ⟦ U ~~ A ⟧ → Code U}{B' : ⟦ U ~~ A' ⟧ → Code U} →
  (pf : `Π A B ≡ `Π A' B') → 
  ∀{a : ⟦ U ~~ A ⟧}{a' : ⟦ U ~~ A' ⟧} →
  subst _ (inj₁ pf) a ≡ a' →
  B a ≡ B' a'
inj₂ refl refl = refl

record ~Σ {n : ℕ} (A : Set) (B : A → Type n) : Set where
  constructor _~,_
  field
    ~fst : A
    ~snd : ⟦ B ~fst ⟧
open ~Σ public

-- ~Ση : ∀{n A}{B : A → Type n} → (p : ~Σ A B) → ~fst p ~, ~snd p ≡ p
-- ~Ση (x ~, y) = refl

{- 

Reference:

[ The original paper that came up with this ]
E. Palmgren. On universes in type theory. In Twenty five years of constructive type theory, 
36, 191 – 204. Oxford University Press, 1998.

[ A simplified formalization ]
C. McBride. Hier soir, an ott hierarchy, Nov. 2011. 
URL http://www.e-pig.org/epilogue/?p=1098.

[ Where this example is found ]
L. Diehl, T. Sheard. Leveling up dependent types: generic programming over a predicative hierarchy of universes.
In Proceedings of the 2013 ACM SIGPLAN Workshop on Dependently-typed Programming, 2013. ACM.

-}





