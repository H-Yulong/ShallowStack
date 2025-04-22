module Machine.Config where

import Lib.Basic as b
open import Lib.Order

open import Model.Shallow
open import Model.Context
open import Model.Labels
open import Model.Stack

open import Machine.Value

open b using (ℕ; _+_)

-- Machine configuration

-- Call frame 
-- Δ is the context of the previous frame
-- δ is the realizing substitution for Δ
record Frame (D : LCon) {Δ : Con} (δ : Sub · Δ) : Set₁ where
  constructor fr
  field
    {len ms ns n d} : ℕ
    {Γ} : Con
    {sΓ} : Ctx Γ len
    {A} : Ty Γ n
    {t} : Tm Γ A
    {η} : Sub · Γ
    {σ} : Stack Γ ms
    {σ'} : Stack Γ ns
    ins : Is D sΓ d (σ ∷ t) σ'
    env : Env D len
    st  : Env D ms
    wf-env : env ⊨ sΓ as η
    wf-st : wf-env ⊢ st ⊨ˢ σ
    ----
    ρ : Sub Δ Γ
    call-compat : η b.≡ ρ ∘ δ


-- Stack of frames
data Sf (D : LCon) : {Γ : Con} → Sub · Γ → ℕ → Set₁ where
  ◆ : Sf D ε 0
  _∷_ : 
    ∀ {Δ n}{δ : Sub · Δ} → 
      Sf D δ n → 
      (frame : Frame D δ) →  
    Sf D (Frame.η frame) (b.suc n)

{- 
  Machine configuration: 
    - [ins] : Instruction sequence
    - [env] : Environment values
    - [st]  : Stack of values
    - [sf]  : Stack of call frames

  Parameters:
    - [Γ, σ, σ' η] : Abstract type parameters, such that
      - Γ ⊢ ins : σ → σ'             (Instruction well-typed)
      - [wf-env] : env ⊨ Γ as η      (Env realizes context, η for env)
      - [wf-st] : wf-env ⊢ st ⊨ˢ σ   (Stack realizes abstract stack)

    - [Δ, δ, ρ, eqc] : Function call parameters, such that
      - δ : · → Δ         
      - sf : Sf D δ       (Stack frame's last context is Δ, realized by δ)
      - ρ : Δ → Γ         (Get current frame via substitution ρ ...)
      - eqc : η ≡ ρ ∘ δ   (... that is compatible with realizations of current and last contexts)
    
    - [len, ms, ns, lf, d] : Lengths and termination marker

-}
record Config (D : LCon) : Set₁ where
  constructor conf
  field
    {len ms ns lf d} : ℕ
    {Γ Δ} : Con
    {sΓ} : Ctx Γ len
    {σ} : Stack Γ ms
    {σ'} : Stack Γ ns
    {η} : Sub · Γ
    {δ} : Sub · Δ
    ins : Is D sΓ d σ σ'
    env : Env D len
    st : Env D ms
    sf : Sf D δ lf
    --
    wf-env : env ⊨ sΓ as η
    wf-st : wf-env ⊢ st ⊨ˢ σ
    --
    ρ : Sub Δ Γ 
    call-compat : η b.≡ ρ ∘ δ

