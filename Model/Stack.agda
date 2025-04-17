module Model.Stack where

open import Agda.Primitive
import Lib.Basic as b 

open import Model.Universe hiding (⟦_⟧)
open import Model.Shallow
open import Model.Labels
open import Model.Context

open b using (ℕ; _+_)
open LCon

-- infixl 5 _∷_
-- infixr 20 _>>_

private variable
  m n ms ns len id : ℕ  
  Γ : Con
--   i j k i' j' k' : Level
--   Γ : Con i
--   A : Ty Γ j
--   B : Ty (Γ ▹ A) k
--   l m n l' m' n' id : b.ℕ
--   sΓ : Ctx Γ l

-- Now, we express a dependendly typed assembly-like stack-machine language,
-- following the idea outlined in "QTAL: A quantitatively and dependendly typed assembly language".
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

-- Better, since the proof of Γ ⊢ σ of Δ is unique if it exists,
-- I can make the two constructors instances, and fire Agda's
-- instance search to automatically find the proof.
-- The trouble of conversion checking is avoided by shallow embedding.

data Stack (Γ : Con) : ℕ → Set₁ where
  ◆ : Stack Γ 0
  _∷_ : ∀{A : Ty Γ n} → Stack Γ ns → Tm Γ A → Stack Γ (b.suc ns)


-- Extensionality transport
Tm-subst : {A A' : Ty Γ n}(t : Tm Γ A)(eq : {γ : Γ} → A γ b.≡ A' γ) → Tm Γ A'
Tm-subst t pf = ~λ (λ γ → b.subst Model.Universe.⟦_⟧ pf (t ~$ γ))
{-
-- Stack typing & interpretation of stacks into substitutions
mutual
  data _⊢_of_as_ {Γ : Con i} (sΓ : Ctx Γ l) : {Δ : Con i'} → Stack Γ n → Ctx Δ l' → Sub Γ Δ → Setω where
    instance
      nil : sΓ ⊢ ◆ of ◆ as ε
      cons : 
        {Δ : Con i'}{sΔ : Ctx Δ l'}{A : Ty Δ j}
        {σ : Stack Γ n}{δ : Sub Γ Δ}{t : Tm Γ (A [ δ ]T)} → 
        ⦃ pf : sΓ ⊢ σ of sΔ as δ ⦄ → 
          sΓ ⊢ (σ ∷ t) of (sΔ ∷ A) as (δ ▻ t)

-- Some stack operations: append, take, drop
_++_ : Stack Γ m → Stack Γ n → Stack Γ (n + m)
σ ++ ◆ = σ
σ ++ (σ' ∷ x) = (σ ++ σ') ∷ x

take : (n : b.ℕ) (σ : Stack Γ (n + m)) → Stack Γ n
take b.zero σ = ◆
take (b.suc n) (σ ∷ x) = (take n σ) ∷ x

drop : (n : b.ℕ) (σ : Stack Γ (n + m)) → Stack Γ m
drop b.zero σ = σ
drop (b.suc n) (σ ∷ x) = drop n σ

-- Stack look-up, which is essentially Fin / de-Bruijn variables
data SVar {Γ : Con i} : Stack Γ n → Ty Γ j → Setω where
  --
  vz : {σ : Stack Γ n}{t : Tm Γ A} → SVar (σ ∷ t) A
  --
  vs : 
    {A' : Ty Γ k}{σ : Stack Γ n}{t : Tm Γ A'} →  
    SVar σ A → SVar (σ ∷ t) A

find : (σ : Stack Γ n) (t : SVar σ A) → Tm Γ A
find (σ ∷ t) vz = t
find (σ ∷ t) (vs x) = find σ x
-}

-- Embedding of Nat literal
nat : b.ℕ → Tm Γ Nat
nat n = ~λ (λ γ → n)

bool : b.Bool → Tm Γ Bool
bool b = ~λ (λ γ → b)

{-
-- Substitution on stacks
_[_]st : {Δ : Con i'} → Stack Δ n → Sub Γ Δ → Stack Γ n
◆ [ ρ ]st = ◆
(σ ∷ t) [ ρ ]st = (σ [ ρ ]st) ∷ t [ ρ ]

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
-- Takes a deep context for easy access to runtime environment (in VAR instruction).
-- Sequencing is made special for easier proofs later.

private variable
  σ : Stack Γ n

mutual

  data Is (D : LCon)(sΓ : Ctx Γ l)(d : b.ℕ) : Stack Γ m → Stack Γ n → Setω where
    --
    RET : Is D sΓ d σ σ
    --
    _>>_ : 
      {σ' : Stack Γ m}{σ'' : Stack Γ n} → 
      Instr D sΓ d σ σ' → Is D sΓ d σ' σ'' → Is D sΓ d σ σ''

  data Instr (D : LCon)(sΓ : Ctx Γ l)(d : b.ℕ) : Stack Γ m → Stack Γ n → Setω where
    NOP : Instr D sΓ d σ σ
    --
    VAR : (x : V sΓ A) → Instr D sΓ d σ (σ ∷ ⟦ x ⟧V)
    --
    POP : {t : Tm Γ A} → Instr D sΓ d (σ ∷ t) σ
    --
    TPOP : Instr D sΓ d (σ ∷ A) σ
    --
    APP : 
        {f : Tm Γ (Π A B)} {a : Tm Γ A} → 
      Instr D sΓ d (σ ∷ f ∷ a) (σ ∷ f $ a)
    --
    CLO : 
        {Δ : Con i'}{sΔ : Ctx Δ l'}
        {A : Ty Δ j'}{B : Ty (Δ ▹ A) k'}
      (n : b.ℕ)
        {σ : Stack Γ (n + m)} 
        {δ : Sub Γ Δ}
      (L : Pi D id sΔ A B)
        ⦃ pf : sΓ ⊢ (take n σ) of sΔ as δ ⦄ →
        ⦃ bound : id b.< d ⦄ →  
      Instr D sΓ d σ (drop n σ ∷ lapp D L δ)
    --
    LIT : (n : b.ℕ) → Instr D sΓ d σ (σ ∷ (nat n))
    --
    TLIT : (A : Ty Γ j) → Instr D sΓ d σ (σ ∷ A)
    --
    SWP :
        {A : Ty Γ j}{A' : Ty Γ k}
        {t : Tm Γ A}{t' : Tm Γ A'} → 
      Instr D sΓ d (σ ∷ t ∷ t') (σ ∷ t' ∷ t)
    --
    ST : (x : SVar σ A) → Instr D sΓ d σ (σ ∷ find σ x)
    --
    INC : {x : Tm Γ Nat} → Instr D sΓ d (σ ∷ x) (σ ∷ suc x)
    --
    ITER : 
      (P : Ty (Γ ▹ Nat) j)
        {z : Tm Γ (P [ ✧ ▻ zero ]T)}
      (Z : Is D sΓ d σ (σ ∷ z))
        {s : Tm (Γ ▹ Nat ▹ P) (P [ p² , (suc 𝟙) ]T)}
      (S : Is D (sΓ ∷ Nat ∷ P) d (σ [ p² ]st ∷ 𝟘 ∷ 𝟙) (σ [ p² ]st ∷ s))
        {x : Tm Γ Nat} → 
      Instr D sΓ d (σ ∷ x) (σ ∷ iter P z s x)
    --
    IF : 
      (P : Ty (Γ ▹ Bool) j)
        {t : Tm Γ (P [ ✧ ▻ true ]T)}
      (T : Is D sΓ d σ (σ ∷ t))
        {f : Tm Γ (P [ ✧ ▻ false ]T)}
      (F : Is D sΓ d σ (σ ∷ f))
        {b : Tm Γ Bool} → 
      Instr D sΓ d (σ ∷ b) (σ ∷ if P t f b) 
    --
    TRUE : Instr D sΓ d σ (σ ∷ true)
    --
    FALSE : Instr D sΓ d σ (σ ∷ false)
    --
    UNIT : Instr D sΓ d σ (σ ∷ tt)
    --
    PAIR : 
        {a : Tm Γ A}{b : Tm Γ (B [ ✧ ▻ a ]T)} → 
      Instr D sΓ d (σ ∷ a ∷ b) (σ ∷ (_,_ {B = B} a b))
    --
    FST : {p : Tm Γ (Σ A B)} → Instr D sΓ d (σ ∷ p) (σ ∷ fst p) 
    --
    SND : {p : Tm Γ (Σ A B)} → Instr D sΓ d (σ ∷ p) (σ ∷ snd p) 
    ----
    REFL : (u : Tm Γ A) → Instr D sΓ d σ (σ ∷ refl u) 
    -- Proofs are erasable at runtime, so we can 
    -- freely create refl as we want
    ----
    JRULE : 
        {u v : Tm Γ A}
      (C : Ty (Γ ▹ A ▹ Id (A [ p ]T) (u [ p ]) 𝟘) k)
      (pf : Tm Γ (Id A u v))
        {w : Tm Γ (C [ ✧ , u , refl u ]T)}
      (W : Is D sΓ d σ (σ ∷ w)) → 
      Instr D sΓ d (σ ∷ pf) (σ ∷ J C w pf) 
    -- Note that we don't allow "extensional equality", like
    -- ∀{σ A u v} → (pf : Id A u v) → Instr D sΓ (σ ∷ u) (σ ∷ v)

-- Procedures
record Proc (D : LCon) (sΓ : Ctx Γ l) (d : b.ℕ) (t : Tm Γ A) : Setω where
  constructor proc
  field
    {len} : b.ℕ
    {σ'} : Stack Γ len
    instr : Is D sΓ d ◆ (σ' ∷ t)

Impl : (D : LCon) → Setω
Impl D = 
  ∀ {id : b.ℕ}
    {i}{Γ : Con i}
    {l}{sΓ : Ctx Γ l}
    {j}{A : Ty Γ j}
    {k}{B : Ty (Γ ▹ A) k} → 
    (lab : Pi D id sΓ A B) → Proc D (sΓ ∷ A) id (interp D lab)

-- Library provides a procedure for each label
record Library : Setω₁ where
  constructor brary
  field
    D : LCon
    --
    impl : Impl D
-}
 