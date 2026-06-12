module Model.Stack where

open import Agda.Primitive
import Lib.Basic as b 

open import Lib.Order

open import Model.Universe hiding (⟦_⟧)
open import Model.Shallow
open import Model.Labels
open import Model.Context

open b using (ℕ; _+_)
open LCon

infixl 5 _∷_
infixr 20 _>>_

private variable
  m n ms ns len len' id id' : ℕ  
  Γ : Con

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

-- Stack typing & interpretation of stacks into substitutions
mutual
  data _⊢_of_as_ {Γ : Con} (sΓ : Ctx Γ len) : ∀{Δ} → Stack Γ ns → Ctx Δ len' → Sub Γ Δ → Set₁ where
    instance
      nil : sΓ ⊢ ◆ of ◆ as ε
      cons : 
        ∀ {Δ}{sΔ : Ctx Δ len'}{A : Ty Δ n}
          {σ : Stack Γ ns}{δ : Sub Γ Δ}{t : Tm Γ (A [ δ ]T)} → 
          ⦃ pf : sΓ ⊢ σ of sΔ as δ ⦄ → 
        sΓ ⊢ (σ ∷ t) of (sΔ ∷ A) as (δ ▻ t)

-- Some stack operations: append, take, drop
_++_ : Stack Γ ms → Stack Γ ns → Stack Γ (ns + ms)
σ ++ ◆ = σ
σ ++ (σ' ∷ x) = (σ ++ σ') ∷ x

take : (ns : b.ℕ) (σ : Stack Γ (ns + ms)) → Stack Γ ns
take b.zero σ = ◆
take (b.suc ns) (σ ∷ x) = (take ns σ) ∷ x

drop : (ns : b.ℕ) (σ : Stack Γ (ns + ms)) → Stack Γ ms
drop b.zero σ = σ
drop (b.suc ns) (σ ∷ x) = drop ns σ

-- Stack look-up, which is essentially Fin / de-Bruijn variables
data SVar {Γ : Con} : Stack Γ ns → Ty Γ n → Set₁ where
  --
  vz : {A : Ty Γ n}{σ : Stack Γ ns}{t : Tm Γ A} → SVar (σ ∷ t) A
  --
  vs : 
    {A A' : Ty Γ n}{σ : Stack Γ ns}{t : Tm Γ A'} →  
    SVar σ A → SVar (σ ∷ t) A

find : {A : Ty Γ n}(σ : Stack Γ ns) (t : SVar σ A) → Tm Γ A
find (σ ∷ t) vz = t
find (σ ∷ t) (vs x) = find σ x

-- Embedding of Nat literal
nat : b.ℕ → Tm Γ Nat
nat n = ~λ (λ γ → n)

bool : b.Bool → Tm Γ Bool
bool b = ~λ (λ γ → b)

-- Substitution on stacks
_[_]st : ∀{Δ} → Stack Δ ns → Sub Γ Δ → Stack Γ ns
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
  σ : Stack Γ ns

mutual

  data Is (D : LCon)(sΓ : Ctx Γ len) : Stack Γ ms → Stack Γ ns → Set₁ where
    --
    RET : Is D sΓ σ σ
    --
    _>>_ : 
      {σ' : Stack Γ ms}{σ'' : Stack Γ ns} → 
      Instr D sΓ σ σ' → Is D sΓ σ' σ'' → Is D sΓ σ σ''

  data Instr (D : LCon)(sΓ : Ctx Γ len) : Stack Γ ms → Stack Γ ns → Set₁ where
    NOP : Instr D sΓ σ σ
    --
    VAR : {A : Ty Γ n}(x : V sΓ A) → Instr D sΓ σ (σ ∷ ⟦ x ⟧V)
    --
    POP : {A : Ty Γ n}{t : Tm Γ A} → Instr D sΓ (σ ∷ t) σ
    --
    -- TPOP : ∀{A : Tm Γ (U n)} → Instr D sΓ (σ ∷ A) σ
    --
    APP : 
        {A : Ty Γ n}{B : Ty (Γ ▹ A) n}
        {f : Tm Γ (Π A B)} {a : Tm Γ A} → 
      Instr D sΓ (σ ∷ f ∷ a) (σ ∷ f $ a)
    --
    CLO : 
      ∀ (ns : b.ℕ)
        {Δ}{sΔ : Ctx Δ ns}
        {A : Ty Δ n}{B : Ty (Δ ▹ A) n}
        {σ : Stack Γ (ns + ms)} 
        {δ : Sub Γ Δ}
      (L : Pi D id sΔ A B)
        ⦃ pf : sΓ ⊢ (take ns σ) of sΔ as δ ⦄ →
      Instr D sΓ σ (drop ns σ ∷ lapp D L δ)
    --
    CLOENV : 
      ∀ {A : Ty Γ n}{B : Ty (Γ ▹ A) n} 
      (L : Pi D id sΓ A B) → 
      Instr D sΓ σ (σ ∷ lapp D L ✧)
    --
    LIT : (n : b.ℕ) → Instr D sΓ σ (σ ∷ (nat n))
    --
    TLIT : (A : Ty Γ n) → Instr D sΓ σ (σ ∷ (c A))
    --
    SWP :
        {A : Ty Γ n}{A' : Ty Γ m}
        {t : Tm Γ A}{t' : Tm Γ A'} → 
      Instr D sΓ (σ ∷ t ∷ t') (σ ∷ t' ∷ t)
    --
    ST : {A : Ty Γ n}(x : SVar σ A) → Instr D sΓ σ (σ ∷ find σ x)
    --
    INC : {x : Tm Γ Nat} → Instr D sΓ (σ ∷ x) (σ ∷ suc x)
    --
    ITER : 
      (P : Ty (Γ ▹ Nat) n)
      (Z : Pi D id sΓ (⊤n n) (P [ p ▻ zero ]T))
      (S : Pi D id' (sΓ ∷ Nat) P (P [ p² ▻ (suc 𝟙) ]T)) 
          {x : Tm Γ Nat} → 
      Instr D sΓ (σ ∷ x) (σ ∷ iter P ((interp D Z) [ ✧ ▻ ttn ]) (interp D S) x)
    --
    UNIT : Instr D sΓ σ (σ ∷ tt)
    --
    PAIR : 
        {A : Ty Γ n}{B : Ty (Γ ▹ A) n}
        {a : Tm Γ A}{b : Tm Γ (B [ ✧ ▻ a ]T)} → 
      Instr D sΓ (σ ∷ a ∷ b) (σ ∷ (_,_ {B = B} a b))
    --
    FST : {A : Ty Γ n}{B : Ty (Γ ▹ A) n}{p : Tm Γ (Σ A B)} → 
      Instr D sΓ (σ ∷ p) (σ ∷ fst p) 
    --
    SND : {A : Ty Γ n}{B : Ty (Γ ▹ A) n}{p : Tm Γ (Σ A B)} → 
      Instr D sΓ (σ ∷ p) (σ ∷ snd p) 
    -- ----
    -- REFL : {A : Ty Γ n}(u : Tm Γ A) → Instr D sΓ σ (σ ∷ refl u) 
    -- -- Proofs are erasable at runtime, so we can 
    -- -- freely create refl as we want
    -- --
    -- JRULE : 
    --     {A : Ty Γ n}{u v : Tm Γ A}
    --   (C : Ty (Γ ▹ A ▹ Id (A [ p ]T) (u [ p ]) 𝟘) n)
    --   (pf : Tm Γ (Id A u v))
    --     {w : Tm Γ (C [ ✧ ▻ u ▻ refl u ]T)}
    --   (W : Is D sΓ σ (σ ∷ w)) → 
    --   Instr D sΓ (σ ∷ pf) (σ ∷ J {u = u} {v} C w pf) 
    -- -- Note that we don't allow "extensional equality", like
    -- -- ∀{σ A u v} → (pf : Id A u v) → Instr D sΓ (σ ∷ u) (σ ∷ v)
    --
    UP : {A : Ty Γ n}{t : Tm Γ A} → 
      Instr D sΓ (σ ∷ t) (σ ∷ ↑ t)
    --
    DOWN : {A : Ty Γ n}{t : Tm Γ A} → 
      Instr D sΓ (σ ∷ ↑ t) (σ ∷ t)


{- Procedures -}
record Proc (D : LCon) (sΓ : Ctx Γ len) {A : Ty Γ n} (id : ℕ) (t : Tm Γ A): Set₁ where
  constructor proc
  field
    {nr} : b.ℕ
    {σ'} : Stack Γ nr
    instr : Is D sΓ ◆ (σ' ∷ t)

Impl : (D : LCon) → Set₁
Impl D = 
  ∀ {id Γ len n}{sΓ : Ctx Γ len}
    {A : Ty Γ n}{B : Ty (Γ ▹ A) n} → 
    (lab : Pi D id sΓ A B) → Proc D (sΓ ∷ A) id (interp D lab)

-- Library provides a procedure for each label
record Library : Set₂ where
  constructor library
  field
    D : LCon
    --
    impl : Impl D
 