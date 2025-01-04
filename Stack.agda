{-# OPTIONS --safe #-}

module Stack where

open import Agda.Primitive
import Basic as lib
open import Shallow
open import Labels

open LCon

infixl 5 _∷_
infixl 20 _>>_

-- Now, we express a dependendropy typed assembly-like stack-machine language,
-- following the idea oudropined in "QTAL: A quantitatively and dependendropy typed assembly language".
-- Types of instruction sequences carry the whole content of the stack
-- before and after the transition.

-- A stack in context Γ is a vector of values in Γ.
-- We need the ability to take part of the stack and turn that into
-- a substitution, i.e. given a stack σ in Γ and some Δ 
-- (the types of free variables for a closure), decide if Γ ⊢ σ : Δ.

-- In the simply-typed situation, each σ satisfies a unique Δ, which is
-- the list of the stack items.
-- It is not the case with dependent types since arbitrary computation
-- exists at type level, for example, (tt , 3) could be a substitution
-- for (Bool, Nat) or (x : Bool, if x then Nat else _).

-- Therefore, I need a judgement Γ ⊢ σ of Δ for showing that 
-- a stack σ in Γ is a valid substitution for Δ.
-- Constructors to this judgement is straightforward:
-- nil: empty stack ◆ is good for empty context ·.
-- cons: given Γ ⊢ σ of Δ, and Γ ⊢ t : A [ σ ], then we have
--       Γ ⊢ (σ ∷ t) of (Δ ▹ A).
--       The type equality is in terms of extnesionality
--       since types in Γ are functions from Γ to Set
--       in the model.

data Stack {i}(Γ : Con i) : lib.ℕ → Setω where
  ◆ : Stack Γ 0
  _∷_ : ∀{j}{A : Ty Γ j}{n} → Stack Γ n → Tm Γ A → Stack Γ (lib.suc n)

-- Extensionality transport
Tm-subst : 
  ∀{i}{Γ : Con i}
   {j}{A A' : Ty Γ j}
   (t : Tm Γ A) → 
   (∀{γ} → A γ lib.≡ A' γ) → 
   Tm Γ A'
Tm-subst t pf γ = lib.coerce pf (t γ)

-- Stack typing & interpretation of stacks into substitutions
mutual
  data _⊢_of_ {i}(Γ : Con i) : ∀{j n} → Stack Γ n → Con j → Setω where
    instance 
      nil : Γ ⊢ ◆ of ·
    instance 
      cons : 
        ∀{j}{Δ : Con j}
         {k}{A : Ty Γ k}{A' : Ty Δ k}
         {n}{σ : Stack Γ n}{t : Tm Γ A} → 
         {{pf : Γ ⊢ σ of Δ}} → 
         {{∀{γ} → A γ lib.≡ (A' [ ⟦ pf ⟧s ]T) γ}} → 
         Γ ⊢ (σ ∷ t) of (Δ ▹ A')

  ⟦_⟧s : 
    ∀{i}{Γ : Con i}
     {j}{Δ : Con j} 
     {n}{σ : Stack Γ n} → 
     Γ ⊢ σ of Δ → Sub Γ Δ
  ⟦_⟧s {σ = σ} nil = ε
  ⟦_⟧s {σ = σ ∷ t} (cons {{pf}} {{x}}) = ⟦ pf ⟧s ▻ Tm-subst t x

-- Some stack operations: append, take, drop
_++_ : ∀{i}{Γ : Con i}{m n} → Stack Γ m → Stack Γ n → Stack Γ (n lib.+ m)
σ ++ ◆ = σ
σ ++ (σ' ∷ x) = (σ ++ σ') ∷ x

take : ∀{i}{Γ : Con i}{m} → (n : lib.ℕ) → Stack Γ (n lib.+ m) → Stack Γ n
take lib.zero σ = ◆
take (lib.suc n) (σ ∷ x) = (take n σ) ∷ x

drop : ∀{i}{Γ : Con i}{m} → (n : lib.ℕ) → Stack Γ (n lib.+ m) → Stack Γ m
drop lib.zero σ = σ
drop (lib.suc n) (σ ∷ x) = drop n σ

-- Stack look-up, which is essentially Fin / de-Bruijn variables
data SVar {i} {Γ : Con i} : ∀{j}{n} → Stack Γ n → Ty Γ j → Setω where
  vz : 
    ∀{j}{A : Ty Γ j}
     {n}{σ : Stack Γ n}{t : Tm Γ A} → 
     SVar (σ ∷ t) A
  vs :
    ∀{j}{A : Ty Γ j}
     {k}{A' : Ty Γ k}
     {n}{σ : Stack Γ n}{t : Tm Γ A'} →  
     SVar σ A → SVar (σ ∷ t) A

find : 
  ∀{i}{Γ : Con i} 
   {j}{A : Ty Γ j}
   {n}(σ : Stack Γ n) →   
   SVar σ A → Tm Γ A
find (σ ∷ t) vz = t
find (σ ∷ t) (vs x) = find σ x

-- Embedding of Nat literal
nat : ∀{i}{Γ : Con i} → lib.ℕ → Tm Γ Nat
nat n γ = n

-- Substitution on stacks
_[_]s : 
  ∀{i}{Γ : Con i}
   {j}{Δ : Con j}{n} →
   Stack Δ n → Sub Γ Δ → Stack Γ n
◆ [ ρ ]s = ◆
(σ ∷ t) [ ρ ]s = (σ [ ρ ]s) ∷ t [ ρ ]

-- Instruction sequences, everything is straightforward in its type.
-- E.g. POP is a sequence that goes from (σ ∷ t) to σ.
-- The most notable one is CLO:
--   Usage: CLO n Lab
--          Lab : name of the defunctionalized label, of type Pi x Δ A B.
--          n   : number of items to take from the stack to form the closure.
--   An instance argument of type Γ ⊢ (take n σ) of Δ is required,
--   showing that the first n items on the stack satisfies the closure's requirement.
--   Such instance can always be uniquely inferred if there exists one -- 
--   it has to be nil if Δ = · and has to be cons if Δ = Δ' ▹ A (and it will keep looking).
-- Another notable one is ITER:
--   Usage: ITER P Z S
--          Exactly the same as the one would expect.
--          P : the return type (a.k.a. major premise).
--          Z : instruction sequence for the zero case, with computation z.
--          S : instruction sequence for the succesor case, with composition s.
--          Given some x : Nat on top of the stack, and the above arguments,
--          ITER P Z S computes iter P z s x.
data Is (D : LCon){i : Level}{Γ : Con i} : 
        ∀{m n} → Stack Γ m → Stack Γ n → Setω where
  POP : 
    ∀{n}{σ : Stack Γ n}
     {j}{A : Ty Γ j}{t : Tm Γ A} → 
     Is D (σ ∷ t) σ
  ----
  TPOP : 
    ∀{n}{σ : Stack Γ n}
     {j}{A : Ty Γ j} → 
     Is D (σ ∷ A) σ
  ---- 
  APP : 
    ∀{n}{σ : Stack Γ n}
     {j}{A : Ty Γ j}
     {k}{B : Ty (Γ ▹ A) k}
     {f : Tm Γ (Π A B)}
     {a : Tm Γ A} → 
     Is D (σ ∷ f ∷ a) (σ ∷ f $ a)
  ----
  CLO : 
    ∀(n : lib.ℕ)
     {m}{σ : Stack Γ (n lib.+ m)}
     {j}{Δ : Con j}
     {k}{A : Ty Δ k}
     {l}{B : Ty (Δ ▹ A) l}
     {x}(L : Pi D x Δ A B)
     {{pf : Γ ⊢ (take n σ) of Δ}} → 
     Is D σ (drop n σ ∷ _⟦_⟧ D L ⟦ pf ⟧s)
  ----
  LIT : 
    ∀{n}{σ : Stack Γ n} → 
     (n : lib.ℕ) → Is D σ (σ ∷ (nat n))
  ----
  TLIT : 
    ∀{n}{j}{σ : Stack Γ n} →
     (A : Ty Γ j) → Is D σ (σ ∷ A)
  ----
  _>>_ : 
    ∀{l}{σ : Stack Γ l}
     {m}{σ' : Stack Γ m}
     {n}{σ'' : Stack Γ n} → 
     Is D σ σ' → Is D σ' σ'' → Is D σ σ''
  ----
  SWP :
    ∀{n}{σ : Stack Γ n}
     {j}{A : Ty Γ j}
     {k}{A' : Ty Γ k}
     {t : Tm Γ A}{t' : Tm Γ A'} → 
     Is D (σ ∷ t ∷ t') (σ ∷ t' ∷ t)
  ----
  ST : 
    ∀{n}{σ : Stack Γ n}
     {j}{A : Ty Γ j}
     (x : SVar σ A) → 
     Is D σ (σ ∷ find σ x)
  ----
  INC : 
    ∀{n}{σ : Stack Γ n}{x : Tm Γ Nat} → 
    Is D (σ ∷ x) (σ ∷ suc x)
  ----
  ITER : 
    ∀{n}{σ : Stack Γ n}
     {j}(P : Ty (Γ ▹ Nat) j)
     {z : Tm Γ (P [ ✧ ▻ zero ]T)}(Z : Is D σ (σ ∷ z)) 
     {s : Tm (Γ ▹ Nat ▹ P) (P [ p² , (suc 𝟙) ]T)}
     (S : Is D {Γ = Γ ▹ Nat ▹ P} (σ [ p² ]s ∷ 𝟘 ∷ 𝟙) (σ [ p² ]s ∷ s))
     {x : Tm Γ Nat} → 
     Is D (σ ∷ x) (σ ∷ iter P z s x)
  ----
  IF : 
    ∀{n}{σ : Stack Γ n}
     {j}(P : Ty (Γ ▹ Bool) j)
     {t : Tm Γ (P [ ✧ ▻ true ]T)}(T : Is D σ (σ ∷ t))
     {f : Tm Γ (P [ ✧ ▻ false ]T)}(T : Is D σ (σ ∷ f))
     {b : Tm Γ Bool} → 
     Is D (σ ∷ b) (σ ∷ if P t f b) 
  ----
  TRUE : 
    ∀{n}{σ : Stack Γ n} → 
    Is D σ (σ ∷ true)
  ----
  FALSE : 
    ∀{n}{σ : Stack Γ n} → 
    Is D σ (σ ∷ false)
  ----
  UNIT : 
    ∀{n}{σ : Stack Γ n} → 
    Is D σ (σ ∷ tt)
  ----
  PAIR : 
    ∀{n}{σ : Stack Γ n} 
     {j}{A : Ty Γ j}
     {k}{B : Ty (Γ ▹ A) k}
     {a : Tm Γ A}{b : Tm Γ (B [ ✧ ▻ a ]T)} → 
     Is D (σ ∷ a ∷ b) (σ ∷ (_,_ {B = B} a b))
  ----
  FST : 
    ∀{n}{σ : Stack Γ n} 
     {j}{A : Ty Γ j}
     {k}{B : Ty (Γ ▹ A) k}
     {p : Tm Γ (Σ A B)} → 
     Is D (σ ∷ p) (σ ∷ fst p) 
  ----
  SND : 
    ∀{n}{σ : Stack Γ n} 
     {j}{A : Ty Γ j}
     {k}{B : Ty (Γ ▹ A) k}
     {p : Tm Γ (Σ A B)} → 
     Is D (σ ∷ p) (σ ∷ snd p) 
  ----
  REFL : 
    ∀{n}{σ : Stack Γ n}
     {j}{A : Ty Γ j}
     (u : Tm Γ A) →
     Is D σ (σ ∷ refl u) 
  -- Proofs are erasable at runtime, so we can 
  -- freely create refl as we want
  ----
  JRULE : 
    ∀{n}{σ : Stack Γ n}
     {j}{A : Ty Γ j}{u v : Tm Γ A}
     {k}(C : Ty (Γ ▹ A ▹ Id (A [ p ]T) (u [ p ]) 𝟘) k)
     (pf : Tm Γ (Id A u v))
     {w : Tm Γ (C [ ✧ , u , refl u ]T)}
     (W : Is D σ (σ ∷ w)) → 
     Is D (σ ∷ pf) (σ ∷ J C w pf) 
  -- Note that we don't allow "extensional equality", like
  -- ∀{σ A u v} → (pf : Id A u v) → Is D (σ ∷ u) (σ ∷ v)
