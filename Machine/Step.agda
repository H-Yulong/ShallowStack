module Machine.Step where

open import Agda.Primitive
import Lib.Basic as lib

open import Model.Shallow
open import Model.Context
open import Model.Labels
open import Model.Stack

open import Machine.Value
open import Machine.Config

open lib using (ℕ; _+_; _≤_)
open LCon

private variable
  i j k i' j' k' : Level
  Γ : Con i
  A : Ty Γ j
  B : Ty (Γ ▹ A) k
  l m n l' m' n' id s lf d : lib.ℕ
  sΓ : Ctx Γ l

-- Helper functions and lemmas

dup : {D : LCon}{σ : Stack Γ n} → Env D n → SVar σ A → Env D (lib.suc n)
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
  {wf-env : sΓ ⊨ env as δ} → 
  wf-env ⊢ σ ⊨ˢ takeᵉ (n + m) st → wf-env ⊢ take n σ ⊨ˢ takeᵉ n (st-assoc {n = n} st)
clo-lem1 {n = ℕ.zero} pf = nil
clo-lem1 {n = ℕ.suc n} {st = st ∷ v} (cons pf eq) rewrite eq = cons (clo-lem1 pf) lib.refl

clo-lem2 : 
  {D : LCon}
  {σ : Stack {i = i} Γ (n + m)}
  {δ : Sub · Γ}
  {env : Env D l}
  {st : Env D (n + m + s)}
  {wf-env : sΓ ⊨ env as δ} → 
  wf-env ⊢ σ ⊨ˢ takeᵉ (n + m) st → wf-env ⊢ drop n σ ⊨ˢ takeᵉ m (dropᵉ n (st-assoc {n = n} st))
clo-lem2 {n = ℕ.zero} pf = pf
clo-lem2 {n = ℕ.suc n} {st = st ∷ v} (cons pf eq) = clo-lem2 pf

-- This intrinsic definition means we have preservation   
data _⊢_↝_ {D : LCon} (I : Impl D) : Config D → Config D → Setω where
  --
  C-NOP : 
      {σ : Stack Γ m}
      {σ' : Stack Γ n}
      {ins : Is D sΓ d σ σ'}
      {env : Env D l}
      {st : Env D (m + s)}
      {sf : Sf D lf}
      {δ : Sub · Γ}
      {wf-env : sΓ ⊨ env as δ}
      {wf-st : wf-env ⊢ σ ⊨ˢ takeᵉ m st} → 
    ---------------------------------------- 
    I ⊢ (conf (NOP >> ins) env st sf wf-env wf-st)
      ↝ (conf ins env st sf wf-env wf-st)
  --
  C-VAR : 
      {x : V sΓ A}
      {σ : Stack Γ m}
      {σ' : Stack Γ n}
      {ins : Is D sΓ d (σ ∷ ⟦ x ⟧V) σ'}
      {env : Env D l}
      {st : Env D (m + s)}
      {δ : Sub · Γ}
      {sf : Sf D lf}
      {wf-env : sΓ ⊨ env as δ}
      {wf-st : wf-env ⊢ σ ⊨ˢ takeᵉ m st} → 
    ----------------------------
    I ⊢ (conf (VAR x >> ins) env st sf wf-env wf-st) 
      ↝ (conf ins env (st ∷ findᵉ env x wf-env) sf wf-env (cons wf-st lib.refl))
  --
  C-ST : 
      {σ : Stack Γ m}
      {σ' : Stack Γ n}
      {x : SVar σ A}
      {ins : Is D sΓ d (σ ∷ find σ x) σ'}
      {δ : Sub · Γ}
      {env : Env D l}
      {st : Env D (m + s)}
      {sf : Sf D lf}
      {wf-env : sΓ ⊨ env as δ}
      {wf-st : wf-env ⊢ σ ⊨ˢ takeᵉ m st} →  
      --------------------------------------
      I ⊢ (conf (ST x >> ins) env st sf wf-env wf-st) 
        ↝ conf ins env (st ∷ findˢ (takeᵉ m st) x wf-st) sf wf-env (cons wf-st lib.refl)
  --
  C-CLO : 
      {σ : Stack {i = i} Γ (n' + m)}
      {σ' : Stack Γ n}
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
      {wf-env : sΓ ⊨ env as δ} 
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
    {σ' : Stack Γ n}
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
    {wf-env : sΓ ⊨ env as δ} 
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
