module DAM.Value where

open import Agda.Primitive

import Lib.Basic as b
open import Lib.Order

open import Model.Universe
open import Model.Shallow
open import Model.Context
open import Model.Stack

open import DAM.Labels
open import DAM.Syntax

private variable
  id m n ms ns nv len : b.ℕ
  Γ : Con
  sΓ : Ctx Γ len
  D : LCon

mutual
  data Val (D : LCon) : {A : Type (b.suc n)} → Tm · (λ {b.tt → A}) → Set₁ where
    --
    lit-⊤ : ∀{n} → Val D (ttn {n = n})
    --
    lit-n : (n : b.ℕ) → Val D (nat n)
    --
    ty : (A : Ty · n) → Val D (c A)
    --
    clo : 
      ∀ {A : Ty Γ n}{B : Ty (Γ ▹ A) n}{δ : Sub · Γ}
        (L : Pi D id sΓ A B)
        (σ : Env D nv) → 
        ⦃ pf : σ ⊨ sΓ as δ ⦄ → 
      -------------------------
      Val D (lapp D L δ)
    lift : {A : Type (b.suc n)}{t : Tm · (λ _ → A)} → Val D t → Val D (↑ t)
    --
    pair : 
      ∀ {A : Ty · n}{B : Ty (· ▹ A) n}
        {t : Tm · A}{t' : Tm · (B [ ✧ ▻ t ]T)} → 
      Val D t → Val D t' → 
      Val D (_,_ {B = B} t t')

  -- Env, list of values, essentially runtime stacks
  data Env (D : LCon) : (nv : b.ℕ) → Set₁ where
    ◆ : Env D b.zero
    _∷_ : {A : Type (b.suc n)}{t : Tm · (λ _ → A)} → Env D nv → Val D t → Env D (b.suc nv)

  -- Env that implements context
  data _⊨_as_ {D : LCon} : Env D len → Ctx Γ len → Sub · Γ → Set₁ where
    nil : ◆ ⊨ ◆ as ε
    --
    cons : 
      {A : Ty Γ n}{sΓ : Ctx Γ len}
      {σ : Env D len}{δ : Sub · Γ}
      {A' : Type (b.suc n)}{t : Tm · (λ _ → A')}{v : Val D t}
      (pf : σ ⊨ sΓ as δ) →
      (pA : A' b.≡ (A [ δ ]T) b.tt) → 
      (σ ∷ v) ⊨ (sΓ ∷ A) as (δ ▻ Tm-subst t pA)

-- Find the term at position x in an env that implements Γ
_[_]V : 
  {A : Ty Γ n}{sΓ : Ctx Γ len}{σ : Env D len}{δ : Sub · Γ}
  (x : V sΓ A) (pf : σ ⊨ sΓ as δ) → Tm · (A [ δ ]T)
_[_]V {δ = δ} x pf = ⟦ x ⟧V [ δ ]

findᵉ : 
  {A : Ty Γ n}{sΓ : Ctx Γ len}{δ : Sub · Γ}
  (env : Env D len)(x : V sΓ A) → 
  (pf : env ⊨ sΓ as δ) → Val D (x [ pf ]V)
findᵉ (env ∷ v) vz (cons pf pA) rewrite pA = v
findᵉ (env ∷ v) (vs x) (cons pf pA) = findᵉ env x pf

takeᵉ : (ns : b.ℕ) → Env D (ns b.+ ms) → Env D ns
takeᵉ b.zero env = ◆
takeᵉ (b.suc n) (env ∷ v) = (takeᵉ n env) ∷ v

dropᵉ : (ns : b.ℕ) → Env D (ns b.+ ms) → Env D ms
dropᵉ b.zero env = env
dropᵉ (b.suc n) (env ∷ v) = dropᵉ n env

-- Judgement: a runtime stack implements a "virtural" stack
data _⊢_⊨ˢ_ {D : LCon} {sΓ : Ctx Γ len} {env : Env D len} {δ : Sub · Γ} 
  (wf : env ⊨ sΓ as δ) : Env D ns → Stack Γ ns → Set₁ where
  --
  nil : wf ⊢ ◆ ⊨ˢ ◆
  --
  cons : 
    ∀ {A : Ty Γ n}{t : Tm Γ A}
      {tA : Type (b.suc n)}
      {σ : Stack Γ ns}{t' : Tm · (λ _ → tA)}
      {st : Env D ns}
      {v : Val D t'} → 
      (pf : wf ⊢ st ⊨ˢ σ) →
      (ptt : tA b.≡ (A [ δ ]T) b.tt) →  
      (eq : t [ δ ] b.≡ Tm-subst t' ptt) → 
    wf ⊢ (st ∷ v) ⊨ˢ (σ ∷ t)  

findˢ : 
  {A : Ty Γ n}{sΓ : Ctx Γ len}{env : Env D len}{δ : Sub · Γ}
  {wf : env ⊨ sΓ as δ}{σ : Stack Γ ns}
  (st : Env D ns)(x : SVar σ A)
  (pf : wf ⊢ st ⊨ˢ σ) → Val D ((find σ x) [ δ ])  
findˢ {σ = σ ∷ t} (st ∷ v) vz (cons pf ptt eq) rewrite ptt | eq = v
findˢ (st ∷ t) (vs x) (cons pf ptt eq) = findˢ st x pf

-- Given:
-- 1. env that implements Γ as δ
-- 2. st that implements σ w.r.t. env
-- 3. Δ such that Γ ⊢ σ of Δ as η
-- Have st implementing Δ as (η ∘ δ)
clo⊨ : 
  {env : Env D len}{Δ : Con}{δ : Sub · Γ}{η : Sub Γ Δ}
  {sΔ : Ctx Δ ns}{st : Env D ns}{σ : Stack Γ ns} → 
  (wf : env ⊨ sΓ as δ) → wf ⊢ st ⊨ˢ σ → sΓ ⊢ σ of sΔ as η → st ⊨ sΔ as (η ∘ δ)
clo⊨ {sΔ = ◆} {◆} {◆} wf wf-st pf = nil
clo⊨ {sΔ = sΔ ∷ A} {st ∷ v} {σ ∷ t} wf (cons wf-st b.refl b.refl) (cons ⦃ pf ⦄) = cons (clo⊨ wf wf-st pf) b.refl

-- Helper functions and lemmas
⊨ˢ-take : 
  ∀ {D : LCon}
    {env : Env D len}
    {δ : Sub · Γ}
    {wf-env : env ⊨ sΓ as δ}
    {st : Env D (m b.+ n)}
    {σ : Stack Γ (m b.+ n)} → 
  wf-env ⊢ st ⊨ˢ σ → 
  wf-env ⊢ takeᵉ m st ⊨ˢ take m σ
⊨ˢ-take {m = b.zero} pf = nil
⊨ˢ-take {m = b.suc m} (cons pf ptt eq) = cons (⊨ˢ-take pf) ptt eq

⊨ˢ-drop : 
  ∀ {D : LCon}
    {env : Env D len}
    {δ : Sub · Γ}
    {wf-env : env ⊨ sΓ as δ}
    {st : Env D (m b.+ n)}
    {σ : Stack Γ (m b.+ n)} → 
  wf-env ⊢ st ⊨ˢ σ → 
  wf-env ⊢ dropᵉ m st ⊨ˢ drop m σ
⊨ˢ-drop {m = b.zero} pf = pf
⊨ˢ-drop {m = b.suc m} (cons pf ptt eq) = ⊨ˢ-drop pf
   