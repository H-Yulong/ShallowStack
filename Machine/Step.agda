module Machine.Step where

import Lib.Basic as b
open import Lib.Order

open import Model.Shallow
open import Model.Context
open import Model.Labels
open import Model.Stack

open import Machine.Value
open import Machine.Config

open b using (ℕ; _+_)
open LCon

private variable
  m n len len' ms ms' ns ns' lf d d' id : ℕ
  Γ : Con
  sΓ : Ctx Γ len

-- This intrinsic definition means we have preservation   
data _⊢_↝_ {D : LCon} (I : Impl D) : Config D → Config D → Set₁ where
  C-NOP : 
      {Δ : Con}
      {δ' : Sub · Δ}
      {σ : Stack Γ ms}
      {σ' : Stack Γ ns}
      {ins : Is D sΓ d σ σ'}
      {env : Env D len}
      {st : Env D ms}
      {sf : Sf D δ' lf}
      {δ : Sub · Γ}
      {η : Sub Δ Γ}
      {wf-env : env ⊨ sΓ as δ}
      {wf-st : wf-env ⊢ st ⊨ˢ σ}
      {call-compat : δ b.≡ η ∘ δ'} → 
    ---------------------------------------- 
    I ⊢ (conf (NOP >> ins) env st sf wf-env wf-st η call-compat)
      ↝ (conf ins env st sf wf-env wf-st η call-compat)
  --
  C-VAR : 
      {Δ : Con}
      {δ' : Sub · Δ}
      {A : Ty Γ n}
      {x : V sΓ A}
      {σ : Stack Γ ms}
      {σ' : Stack Γ ns}
      {ins : Is D sΓ d (σ ∷ ⟦ x ⟧V) σ'}
      {env : Env D len}
      {st : Env D ms}
      {δ : Sub · Γ}
      {sf : Sf D δ' lf}
      {wf-env : env ⊨ sΓ as δ}
      {wf-st : wf-env ⊢ st ⊨ˢ σ}
      {η : Sub Δ Γ}
      {call-compat : δ b.≡ η ∘ δ'} → 
    ----------------------------
    I ⊢ (conf (VAR x >> ins) env st sf wf-env wf-st η call-compat) 
      ↝ (conf ins env (st ∷ findᵉ env x wf-env) sf wf-env (cons wf-st b.refl b.refl) η call-compat)
  --
  C-ST : 
      {Δ : Con}
      {δ' : Sub · Δ}
      {A : Ty Γ n}
      {σ : Stack Γ ms}
      {σ' : Stack Γ ns}
      {x : SVar σ A}
      {ins : Is D sΓ d (σ ∷ find σ x) σ'}
      {δ : Sub · Γ}
      {env : Env D len}
      {st : Env D ms}
      {sf : Sf D δ' lf}
      {wf-env : env ⊨ sΓ as δ}
      {wf-st : wf-env ⊢ st ⊨ˢ σ}
      {η : Sub Δ Γ}
      {call-compat : δ b.≡ η ∘ δ'} →  
      --------------------------------------
      I ⊢ conf (ST x >> ins) env st sf wf-env wf-st η call-compat
        ↝ conf ins env (st ∷ findˢ st x wf-st) sf wf-env (cons wf-st b.refl b.refl) η call-compat
  --
  C-CLO : 
      {Δ' : Con}
      {δ' : Sub · Δ'}
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
      {sf : Sf D δ' lf}
      {wf-env : env ⊨ sΓ as δ} 
      {wf-st : wf-env ⊢ st ⊨ˢ σ}
      {η' : Sub Δ' Γ}
      {call-compat : δ b.≡ η' ∘ δ'} →  
      ⦃ pf : sΓ ⊢ (take ms' σ) of sΔ as η ⦄ →
      ⦃ bound : id < d ⦄ → 
      {ins : Is D sΓ d (drop ms' σ ∷ lapp D L η) σ'} →  
    ------------------------------ 
    let closure = clo L (takeᵉ ms' st) ⦃ clo⊨ wf-env (⊨ˢ-take wf-st) pf ⦄ in
    I ⊢ conf (CLO ms' L >> ins) env st sf wf-env wf-st η' call-compat
      ↝ conf ins env (dropᵉ ms' st ∷ closure) sf wf-env (cons (⊨ˢ-drop wf-st) b.refl (lapp[] D)) η' call-compat
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
    {Δ' : Con}
    {δ' : Sub · Δ'}
    {δ : Sub · Γ}
    {env : Env D len}
    {st : Env D ms}
    {sf : Sf D δ' lf}
    {wf-env : env ⊨ sΓ as δ} 
    {wf-st : wf-env ⊢ st ⊨ˢ σ}
    {η' : Sub Δ' Γ}
    {call-compat : δ b.≡ η' ∘ δ'} 
    -- abstract values
    {t : Tm Γ (A [ η ]T)}
    -- concrete values
    {env' : Env D len'}
    {v : Val D (t [ δ ])}
    ⦃ pf : env' ⊨ sΔ as (η ∘ δ) ⦄ → 
    -- instruction
    {ins : Is D sΓ d (σ ∷ (lapp D L η) $ t) σ'} →  
    -----------------
    let wf-st' = (cons (cons wf-st b.refl (lapp[] D)) b.refl b.refl) in
    let new-fr = fr ins env st wf-env wf-st η' call-compat  in
    I ⊢ conf (APP {f = lapp D L η} >> ins) env (st ∷ clo L env' ∷ v) sf wf-env wf-st' η' call-compat
      ↝ conf (Proc.instr (I L)) (env' ∷ v) ◆ (sf ∷ new-fr) (cons pf) nil (η ▻ t) b.refl
  --
  C-RET : 
    -- callee env
    {Γ : Con}
    {sΓ : Ctx Γ len}
    {env : Env D len}
    {δ : Sub · Γ}
    {wf-env : env ⊨ sΓ as δ}
    -- callee stack
    {σ : Stack Γ ns}
    {st : Env D ns}
    {wf-st : wf-env ⊢ st ⊨ˢ σ}
    -- previous frames
    {Ω : Con}
    {ω : Sub · Ω}
    {sf : Sf D ω lf}
    -- top frame
    {fr : Frame D ω}
    -- callee compat
    {η : Sub (Frame.Γ fr) Γ}
    {call-compat : δ b.≡ η ∘ (Frame.δ fr)}
    -- return value
    {v : Val D ((Frame.t fr) [ Frame.δ fr ])}
    → 
    I ⊢ conf (RET {d = d}) env (st ∷ v) (sf ∷ fr) wf-env (cons wf-st b.refl b.refl) η call-compat
      ↝ conf (Frame.ins fr) (Frame.env fr) (Frame.st fr ∷ v) sf (Frame.wf-env fr) (cons (Frame.wf-st fr) b.refl b.refl) (Frame.η fr) (Frame.call-compat fr)


