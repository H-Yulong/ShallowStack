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
open LCon

private variable
  m n len len' ms ns ms' lf d id : ℕ
  Γ : Con
  sΓ : Ctx Γ len

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
  --
  C-CLO : 
      {σ : Stack Γ (ms' + ms)}
      {σ' : Stack Γ ns}
      {Δ : Con}
      {sΔ : Ctx Δ ms'}
      {A : Ty Δ n}
      {B : Ty (Δ ▹ A) n}
      {L : Pi D id sΔ A B}
      {δ : Sub · Γ}
      {η : Sub Γ Δ}
      {env : Env D len}
      {st : Env D (ms' + ms)}
      {sf : Sf D lf}
      {wf-env : env ⊨ sΓ as δ} 
      {wf-st : wf-env ⊢ st ⊨ˢ σ} →  
      ⦃ pf : sΓ ⊢ (take ms' σ) of sΔ as η ⦄ →
      ⦃ bound : id < d ⦄ → 
      {ins : Is D sΓ d (drop ms' σ ∷ lapp D L η) σ'} →  
    ------------------------------ 
    let closure = clo L (takeᵉ ms' st) ⦃ clo⊨ wf-env (⊨ˢ-take wf-st) pf ⦄ in
    I ⊢ conf (CLO ms' L >> ins) env st sf wf-env wf-st 
      ↝ conf ins env (dropᵉ ms' st ∷ closure) sf wf-env (cons (⊨ˢ-drop wf-st) lib.refl (lapp[] D))
  --
  C-APP : 
    -- stacks
    {σ : Stack Γ ms}
    {σ' : Stack Γ ns}
    -- label setup
    {Δ : Con}
    {sΔ : Ctx Δ len'}
    {A : Ty Δ n}
    {B : Ty (Δ ▹ A) n}
    {L : Pi D id sΔ A B}
    {η : Sub Γ Δ}
    -- config
    {δ : Sub · Γ}
    {env : Env D len}
    {st : Env D ms}
    {sf : Sf D lf}
    {wf-env : env ⊨ sΓ as δ} 
    {wf-st : wf-env ⊢ st ⊨ˢ σ}
    -- -- abstract values
    {t : Tm Γ (A [ η ]T)}
    -- -- concrete values
    {env' : Env D len'}
    {v : Val D (t [ δ ])}
    ⦃ pf : env' ⊨ sΔ as (η ∘ δ) ⦄ → 
    -- -- ⦃ pf : sΓ ⊢ σ of sΔ as η ⦄ →
    {ins : Is D sΓ d (σ ∷ (lapp D L η) $ t) σ'} →  
    -----------------
    let wf-st' = (cons (cons wf-st lib.refl (lapp[] D)) lib.refl lib.refl) in
    I ⊢ conf (APP {f = lapp D L η} >> ins) env (st ∷ clo L env' ∷ v) sf wf-env wf-st'
      ↝ conf (Proc.instr (I L)) (env' ∷ v) ◆ (sf ∷ fr ins env {!  st !}) (cons pf) nil
    
    
    -- I ⊢ conf (APP {f = lapp D L η} >> ins) env (st ∷ clo L env' ∷ v) sf wf-env (cons (cons wf-st (lib.sym (lapp[] D))) lib.refl) 
      -- ↝ conf (Proc.instr (I L)) (env' ∷ v) st (sf ∷ fr ins env (m + s)) (cons pf) nil
