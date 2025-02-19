{-# OPTIONS --safe #-}

module Theory where

open import Agda.Primitive
import Basic as lib
open import Shallow
open import Labels
open import Context
open import Stack

open LCon

-- Representation of runtime values,
-- re-using shallow-embedded syntax as much as possible

-- I'll do pairs later, that has a few more nasty judgements.

mutual
  data Val (D : LCon) : ∀{i}{A : Ty · i} → Tm · A → Setω where
    lit-b : (b : lib.Bool) → Val D (bool b)
    lit-n : (n : lib.ℕ) → Val D (nat n)
    ty : ∀{i}(A : Ty · i) → Val D A
    ----
    clo : 
      ∀ {i}{Γ : Con i}
        {n}{sΓ : Ctx Γ n}
        {j}{A : Ty Γ j}
        {k}{B : Ty (Γ ▹ A) k}
        {id}(L : Pi D id sΓ A B)
        (σ : Env D n) → ⦃ pf : sΓ ⊨ σ ⦄ → Val D (_⟦_⟧ D L ⟦ pf ⟧⊨)

  -- Env, list of values, essentially runtime stacks
  data Env (D : LCon) : (n : lib.ℕ) → Setω where
    ◆ : Env D lib.zero
    _∷_ : ∀{n i}{A : Ty · i}{t : Tm · A} → Env D n → Val D t → Env D (lib.suc n)

  -- Env that implements context
  data _⊨_ {D : LCon} : ∀{i n}{Γ : Con i} → Ctx Γ n → Env D n → Setω where
    instance
      nil : ◆ ⊨ ◆
    instance
      cons : 
        ∀{i}{Γ : Con i}
         {j}{A : Ty · j}{A' : Ty Γ j}
         {n}{sΓ : Ctx Γ n}{σ : Env D n}
         {t : Tm · A}{v : Val D t}
         ⦃ pf : sΓ ⊨ σ ⦄ →
         ⦃ eq : A lib.≡ (A' [ ⟦ pf ⟧⊨ ]T) ⦄ → 
         ((sΓ ∷ A') ⊨ (σ ∷ v))
    -- Note the actual equality used here.
    -- Since we're only comparing closed types and terms,
    -- it's convinent to do so as we have ({t : ⊤} → f t ≡ g t) → f ≡ g.
    -- Has nice computational behaviour.

  ⟦_⟧⊨ : 
    ∀{D : LCon}
     {i}{Γ : Con i}
     {n}{sΓ : Ctx Γ n}{σ : Env D n} → 
     (sΓ ⊨ σ) → Sub · Γ
  ⟦_⟧⊨ nil = ε
  ⟦_⟧⊨ {σ = _∷_ {t = t} σ v} (cons ⦃ pf ⦄ ⦃ x ⦄) = ⟦ pf ⟧⊨ ▻ Tm-subst t (lib.cong-app x)

-- Find the term which implements Γ at position x
_[_]V : 
  ∀ {D : LCon}
    {i}{Γ : Con i}
    {j}{A : Ty Γ j}
    {n}{sΓ : Ctx Γ n}{σ : Env D n} →
    (x : V sΓ A) → (pf : sΓ ⊨ σ) → Tm · (A [ ⟦ pf ⟧⊨ ]T)
x [ pf ]V = ⟦ x ⟧V [ ⟦ pf ⟧⊨ ]

Val-subst : 
  ∀ {D : LCon}
    {i}{A A' : Ty · i}{t : Tm · A}
    (v : Val D t) → 
    (pf : A lib.≡ A') → Val D (Tm-subst t (lib.cong-app pf))
Val-subst v lib.refl = v
  
findᵉ : 
  ∀ {D : LCon}
    {i}{Γ : Con i}
    {j}{A : Ty Γ j}
    {n}{sΓ : Ctx Γ n}
    (σ : Env D n)(x : V sΓ A) → 
    ⦃ pf : sΓ ⊨ σ ⦄ → Val D (x [ pf ]V)
findᵉ {D} (σ ∷ v) vz ⦃ cons ⦃ eq = eq ⦄ ⦄ = Val-subst v eq
findᵉ (σ ∷ v) (vs x) ⦃ cons ⦃ pf = pf ⦄ ⦄ = findᵉ σ x ⦃ pf ⦄

takeᵉ : ∀{D : LCon}{m} → (n : lib.ℕ) → Env D (n lib.+ m) → Env D n
takeᵉ lib.zero env = ◆
takeᵉ (lib.suc n) (env ∷ v) = (takeᵉ n env) ∷ v

dropᵉ : ∀{D : LCon}{m} → (n : lib.ℕ) → Env D (n lib.+ m) → Env D m
dropᵉ lib.zero env = env
dropᵉ (lib.suc n) (env ∷ v) = dropᵉ n env

-- dup : 
--   ∀ {D : LCon}
--     {i}{Γ : Con i}
--     {n}{σ : Stack Γ n}
--     {j}{A : Ty Γ j} → 
--     Env D n → SVar σ A → Env D (lib.suc n)
-- dup (env ∷ t) vz = env ∷ t ∷ t
-- dup (env ∷ t) (vs x) = (dup env x) ∷ t

-- Procedures
data Proc  
  (D : LCon)
  {i}{Γ : Con i}
  {l}(sΓ : Ctx Γ l)
  {m}(σ : Stack Γ m)
  {j : Level}{A : Ty Γ j}(t : Tm Γ A) : Setω where
  proc : ∀{n}{σ' : Stack Γ n} → Is D sΓ σ (σ' ∷ t) → Proc D sΓ σ t

-- Library provides a procedure for each label
record Library : Setω where
  field
    D : LCon
    ----
    impl : 
      ∀{i}{Γ : Con i}
       {j}{A : Ty Γ j}
       {k}{B : Ty (Γ ▹ A) k}
       {l}{sΓ : Ctx Γ l}
       {id}(lab : Pi D id sΓ A B)
       {m}{σ : Stack (Γ ▹ A) m} → 
       Proc D (sΓ ∷ A) σ (interp D lab)
 