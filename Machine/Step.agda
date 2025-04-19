module Machine.Step where

import Lib.Basic as lib
open import Lib.Order

open import Model.Shallow
open import Model.Context
open import Model.Labels
open import Model.Stack

open import Machine.Value
open import Machine.Config

open lib using (ℕ; _+_)

private variable
  m n len ms ns lf d : ℕ
  Γ : Con
  sΓ : Ctx Γ len

-- Helper functions and lemmas
{-
dup : {D : LCon}{σ : Stack Γ ns} → Env D n → SVar σ A → Env D (lib.suc n)
dup (env ∷ t) vz = env ∷ t ∷ t
dup (env ∷ t) (vs x) = (dup env x) ∷ t

st-assoc : ∀{D n m s} → Env D ((n + m) + s) → Env D (n + (m + s))
st-assoc {D} {ℕ.zero} {m} {s} st = st
st-assoc {D} {ℕ.suc n} {m} {s} (st ∷ v) = st-assoc {n = n} st ∷ v

clo-lem1 : 
  {D : LCon}
  {σ : Stack {i = i} Γ (n + m)}
  {δ : Sub · Γ}
  {env : Env D l}
  {st : Env D (n + m + s)}
  {wf-env : env ⊨ sΓ as δ} → 
  wf-env ⊢ σ ⊨ˢ takeᵉ (n + m) st → wf-env ⊢ take n σ ⊨ˢ takeᵉ n (st-assoc {n = n} st)
clo-lem1 {n = ℕ.zero} pf = nil
clo-lem1 {n = ℕ.suc n} {st = st ∷ v} (cons pf eq) rewrite eq = cons (clo-lem1 pf) lib.refl

clo-lem2 : 
  {D : LCon}
  {σ : Stack {i = i} Γ (n + m)}
  {δ : Sub · Γ}
  {env : Env D l}
  {st : Env D (n + m + s)}
  {wf-env : env ⊨ sΓ as δ} → 
  wf-env ⊢ σ ⊨ˢ takeᵉ (n + m) st → wf-env ⊢ drop n σ ⊨ˢ takeᵉ m (dropᵉ n (st-assoc {n = n} st))
clo-lem2 {n = ℕ.zero} pf = pf
clo-lem2 {n = ℕ.suc n} {st = st ∷ v} (cons pf eq) = clo-lem2 pf
-}

-- This intrinsic definition means we have preservation   
data _⊢_↝_ {D : LCon} (I : Impl D) : Config D → Config D → Set₁ where
  C-NOP : 
      {σ : Stack Γ ms}
      {σ' : Stack Γ ns}
      {ins : Is D sΓ d σ σ'}
      {env : Env D len}
      {st : Env D ms}
      {sf : Sf D lf}
      {δ : Sub · Γ}
      {wf-env : env ⊨ sΓ as δ}
      {wf-st : wf-env ⊢ st ⊨ˢ σ} → 
    ---------------------------------------- 
    I ⊢ (conf (NOP >> ins) env st sf wf-env wf-st)
      ↝ (conf ins env st sf wf-env wf-st)
  --
  C-VAR : 
      {A : Ty Γ n}
      {x : V sΓ A}
      {σ : Stack Γ ms}
      {σ' : Stack Γ ns}
      {ins : Is D sΓ d (σ ∷ ⟦ x ⟧V) σ'}
      {env : Env D len}
      {st : Env D ms}
      {δ : Sub · Γ}
      {sf : Sf D lf}
      {wf-env : env ⊨ sΓ as δ}
      {wf-st : wf-env ⊢ st ⊨ˢ σ} → 
    ----------------------------
    I ⊢ (conf (VAR x >> ins) env st sf wf-env wf-st) 
      ↝ (conf ins env (st ∷ findᵉ env x wf-env) sf wf-env (cons wf-st lib.refl lib.refl))
  --
  C-ST : 
      {A : Ty Γ n}
      {σ : Stack Γ ms}
      {σ' : Stack Γ ns}
      {x : SVar σ A}
      {ins : Is D sΓ d (σ ∷ find σ x) σ'}
      {δ : Sub · Γ}
      {env : Env D len}
      {st : Env D ms}
      {sf : Sf D lf}
      {wf-env : env ⊨ sΓ as δ}
      {wf-st : wf-env ⊢ st ⊨ˢ σ} →  
      --------------------------------------
      I ⊢ (conf (ST x >> ins) env st sf wf-env wf-st) 
        ↝ conf ins env (st ∷ findˢ st x wf-st) sf wf-env (cons wf-st lib.refl lib.refl)
  {--
  C-CLO : 
      {σ : Stack {i = i} Γ (n' + m)}
      {σ' : Stack Γ ns}
      {Δ : Con i'}
      {sΔ : Ctx Δ n'}
      {A : Ty Δ j'}
      {B : Ty (Δ ▹ A) k'}
      {L : Pi D id sΔ A B}
      {δ : Sub · Γ}
      {η : Sub Γ Δ}
      {env : Env D l}
      {st : Env D (n' + m + s)}
      {sf : Sf D lf}
      {wf-env : env ⊨ sΓ as δ} 
      {wf-st : wf-env ⊢ σ ⊨ˢ takeᵉ (n' + m) st} →  
      ⦃ pf : sΓ ⊢ (take n' σ) of sΔ as η ⦄ →
      ⦃ bound : id lib.< d ⦄ → 
      {ins : Is D sΓ d (drop n' σ ∷ lapp D L η) σ'} →  
    ------------------------------
    let st' = st-assoc {n = n'} st in
    let val = clo L (takeᵉ n' st') ⦃ clo⊨ wf-env (clo-lem1 wf-st) pf ⦄ in
    let st'' = dropᵉ n' st' ∷ val in
    I ⊢ conf (CLO n' L >> ins) env st sf wf-env wf-st
      ↝ conf ins env st'' sf wf-env (cons (clo-lem2 wf-st) (lib.sym (lapp[] D)))
  --
  C-APP : 
    -- stacks
    {σ : Stack {i = i} Γ m}
    {σ' : Stack Γ ns}
    -- label setup
    {Δ : Con i'}
    {sΔ : Ctx Δ l'}
    {A : Ty Δ j'}
    {B : Ty (Δ ▹ A) k'}
    {L : Pi D id sΔ A B}
    {η : Sub Γ Δ}
    -- config
    {δ : Sub · Γ}
    {env : Env D l}
    {st : Env D (m + s)}
    {sf : Sf D lf}
    {wf-env : env ⊨ sΓ as δ} 
    {wf-st : wf-env ⊢ σ ⊨ˢ (takeᵉ m st)}
    -- abstract values
    {t : Tm Γ (A [ η ]T)}
    -- concrete values
    {env' : Env D l'}
    {v : Val D (t [ δ ])}
    ⦃ pf : sΔ ⊨ env' as (η ∘ δ) ⦄ → 
    -- ⦃ pf : sΓ ⊢ σ of sΔ as η ⦄ →
    {ins : Is D sΓ d (σ ∷ (lapp D L η) $ t) σ'} →  
    -----------------
    I ⊢ conf (APP {f = lapp D L η} >> ins) env (st ∷ clo L env' ∷ v) sf wf-env (cons (cons wf-st (lib.sym (lapp[] D))) lib.refl) 
      ↝ conf (Proc.instr (I L)) (env' ∷ v) st (sf ∷ fr ins env (m + s)) (cons pf) nil
-}