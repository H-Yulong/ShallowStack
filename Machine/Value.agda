module Machine.Value where

open import Agda.Primitive
import Lib.Basic as lib
open import Model.Shallow
open import Model.Context
open import Model.Labels
open import Model.Stack

open LCon

private variable
  i j k i' j' k' : Level
  Γ : Con i
  A : Ty Γ j
  B : Ty (Γ ▹ A) k
  l m n l' m' n' id : lib.ℕ
  sΓ : Ctx Γ l
  D : LCon

-- Representation of runtime values,
-- which knows what value in the syntax it implements.
-- (Treat pairs later)

mutual
  data Val (D : LCon) : {A : Ty · i} → Tm · A → Setω where
    --
    lit-b : (b : lib.Bool) → Val D (bool b)
    --
    lit-n : (n : lib.ℕ) → Val D (nat n)
    --
    ty : (A : Ty · i) → Val D A
    --
    clo : 
      {B : Ty (Γ ▹ A) j}
      {δ : Sub · Γ}
      (L : Pi D id sΓ A B)
      (σ : Env D n) → 
      ⦃ pf : sΓ ⊨ σ as δ ⦄ → 
      Val D (lapp D L δ)

  -- Env, list of values, essentially runtime stacks
  data Env (D : LCon) : (n : lib.ℕ) → Setω where
    ◆ : Env D lib.zero
    _∷_ : {A : Ty · i}{t : Tm · A} → Env D n → Val D t → Env D (lib.suc n)

  -- Env that implements context
  data _⊨_as_ {D : LCon} : {Γ : Con i} → Ctx Γ n → Env D n → Sub · Γ → Setω where
    nil : ◆ ⊨ ◆ as ε
    --
    cons : 
      {A : Ty Γ j}{sΓ : Ctx Γ n}
      {σ : Env D n}{δ : Sub · Γ}
      {t : Tm · (A [ δ ]T)}{v : Val D t}
      (pf : sΓ ⊨ σ as δ) →
      ((sΓ ∷ A) ⊨ (σ ∷ v) as (δ ▻ t))

-- Find the term at position x in an env that implements Γ
_[_]V : 
  {sΓ : Ctx Γ n}{σ : Env D n}{δ : Sub · Γ}
  (x : V sΓ A) (pf : sΓ ⊨ σ as δ) → Tm · (A [ δ ]T)
_[_]V {δ = δ} x pf = ⟦ x ⟧V [ δ ]

Val-subst : 
  {A A' : Ty · i}{t : Tm · A}
  (v : Val D t) (pf : A lib.≡ A') → Val D (Tm-subst t (lib.cong-app pf))
Val-subst v lib.refl = v

findᵉ : 
  {sΓ : Ctx Γ n}{δ : Sub · Γ}
  (env : Env D n)(x : V sΓ A) → 
  (pf : sΓ ⊨ env as δ) → Val D (x [ pf ]V)
findᵉ (env ∷ v) vz (cons pf) = v
findᵉ (env ∷ v) (vs x) (cons pf) = findᵉ env x pf

takeᵉ : (n : lib.ℕ) → Env D (n lib.+ m) → Env D n
takeᵉ lib.zero env = ◆
takeᵉ (lib.suc n) (env ∷ v) = (takeᵉ n env) ∷ v

dropᵉ : (n : lib.ℕ) → Env D (n lib.+ m) → Env D m
dropᵉ lib.zero env = env
dropᵉ (lib.suc n) (env ∷ v) = dropᵉ n env

-- Judgement: a runtime stack implements a "virtural" stack
data _⊢_⊨ˢ_ {D : LCon} {sΓ : Ctx Γ l} {env : Env D l} {δ : Sub · Γ} 
  (wf : sΓ ⊨ env as δ) : Stack Γ n → Env D n → Setω where
----
  nil : wf ⊢ ◆ {Γ = Γ} ⊨ˢ ◆
  --
  cons : 
    {σ : Stack Γ n}{t : Tm Γ A}{t' : Tm · (A [ δ ]T)}
    {st : Env D n}{v : Val D t'} → 
    (pf : wf ⊢ σ ⊨ˢ st) → 
    (eq : t' lib.≡ t [ δ ]) → 
    wf ⊢ (σ ∷ t) ⊨ˢ (st ∷ v)  
  -- I have to take the explicit equality here because function label's congruence
  -- under substitution is not refl, since label contexts are given as a signature.
  -- It doesn't hurt the development so far...

findˢ : 
  {sΓ : Ctx Γ l}{env : Env D l}{δ : Sub · Γ}
  {wf : sΓ ⊨ env as δ}{σ : Stack Γ n}
  (st : Env D n)(x : SVar σ A)
  (pf : wf ⊢ σ ⊨ˢ st) → Val D ((find σ x) [ δ ])  
findˢ {σ = σ ∷ t} (st ∷ v) vz (cons pf eq) rewrite eq = v
findˢ (st ∷ t) (vs x) (cons pf _) = findˢ st x pf

-- Given:
-- 1. env that implements Γ as δ
-- 2. st that implements σ w.r.t. env
-- 3. Δ such that Γ ⊢ σ of Δ as η
-- Have st implementing Δ as (η ∘ δ)
clo⊨ : 
  {env : Env D l}{Δ : Con i'}{δ : Sub · Γ}{η : Sub Γ Δ}
  {sΔ : Ctx Δ n}{st : Env D n}{σ : Stack Γ n} → 
  (wf : sΓ ⊨ env as δ) → wf ⊢ σ ⊨ˢ st → sΓ ⊢ σ of sΔ as η → sΔ ⊨ st as (η ∘ δ)
clo⊨ {sΔ = ◆} {◆} {◆} wf wf-st pf = nil
clo⊨ {sΔ = sΔ ∷ A} {st ∷ v} {σ ∷ t} wf (cons wf-st eq) (cons ⦃ pf ⦄) rewrite eq
  = cons (clo⊨ wf wf-st pf)

⊨ˢ-take : 
  {sΓ : Ctx Γ l}{env : Env D l}{δ : Sub · Γ}
  {wf : sΓ ⊨ env as δ}{σ : Stack Γ (n lib.+ m)}{st : Env D (n lib.+ m)} → 
  wf ⊢ σ ⊨ˢ st → wf ⊢ (take n σ) ⊨ˢ (takeᵉ n st)
⊨ˢ-take {n = lib.zero} pf = nil
⊨ˢ-take {n = lib.suc n} (cons pf eq) rewrite eq = cons (⊨ˢ-take pf) lib.refl


 
 