{-# OPTIONS --safe #-}

module Stack where

open import Agda.Primitive
import Basic as lib
open import Shallow
open import ShallowDFC

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
data Is {i : Level}{Γ : Con i} : ∀{m n} → Stack Γ m → Stack Γ n → Setω where
  POP : 
    ∀{j}{A : Ty Γ j}
     {n}{σ : Stack Γ n}
     {t : Tm Γ A} → Is (σ ∷ t) σ
  ----
  TPOP : 
    ∀{j}{n}{σ : Stack Γ n}
     {A : Ty Γ j} → Is (σ ∷ A) σ
  ----
  APP : 
    ∀{j}{A : Ty Γ j}
     {k}{B : Ty (Γ ▹ A) k}
     {n}{σ : Stack Γ n}
     {f : Tm Γ (Π A B)}
     {a : Tm Γ A} → 
     Is (σ ∷ f ∷ a) (σ ∷ f $ a)
  ----
  CLO : 
    ∀{j}{Δ : Con j}
     {k}{A : Ty Δ k}
     {l}{B : Ty (Δ ▹ A) l}
     (n : lib.ℕ)
     {m}{σ : Stack Γ (n lib.+ m)}
     {x}(L : Pi x Δ A B) →
     {{pf : Γ ⊢ (take n σ) of Δ}} → 
     Is σ ((drop n σ) ∷ L ⟦ ⟦ pf ⟧s ⟧)
  ----
  LIT : 
    ∀{n}{σ : Stack Γ n} → 
     (n : lib.ℕ) → Is σ (σ ∷ (nat n))
  ----
  TLIT : 
    ∀{n}{j}{σ : Stack Γ n} →
     (A : Ty Γ j) → Is σ (σ ∷ A)
  ----
  _>>_ : 
    ∀{l m n}
     {σ : Stack Γ l}
     {σ' : Stack Γ m}
     {σ'' : Stack Γ n} → 
     Is σ σ' → Is σ' σ'' → Is σ σ''
  ----
  SWP :
    ∀{j}{A : Ty Γ j}
     {k}{A' : Ty Γ k}
     {n}{σ : Stack Γ n}
     {t : Tm Γ A}{t' : Tm Γ A'} → 
     Is (σ ∷ t ∷ t') (σ ∷ t' ∷ t)
  ----
  ST : 
    ∀{j}{A : Ty Γ j}
     {n}{σ : Stack Γ n} → 
     (x : SVar σ A) → 
     Is σ (σ ∷ find σ x)
 