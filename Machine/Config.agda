module Machine.Config where

import Lib.Basic as lib
open import Lib.Order

open import Model.Shallow
open import Model.Context
open import Model.Labels
open import Model.Stack

open import Machine.Value

open lib using (ℕ; _+_)

-- Machine configuration

-- Call frame 
record Frame (D : LCon) : Set₁ where
  constructor fr
  field
    {len ms ns n d} : ℕ
    {Γ Δ} : Con
    {sΓ} : Ctx Γ len
    {A} : Ty Γ n
    {t} : Tm Γ A
    {δ} : Sub · Γ
    {σ} : Stack Γ ms
    {σ'} : Stack Γ ns
    ins : Is D sΓ d (σ ∷ t) σ'
    env : Env D len
    st  : Env D ms
    sub : Sub Γ Δ
    wf-env : env ⊨ sΓ as δ
    wf-st : wf-env ⊢ st ⊨ˢ σ

-- Stack of frames
data Sf (D : LCon) : ℕ → Set₁ where
  ◆ : Sf D 0
  _∷_ : ∀{n} → Sf D n → Frame D → Sf D (lib.suc n)

-- Machine state: instr, env, stack, and frame stack
record Config (D : LCon) : Set₁ where
  constructor conf
  field
    {len ms ns lf d} : ℕ
    {Γ} : Con
    {sΓ} : Ctx Γ len
    {σ} : Stack Γ ms
    {σ'} : Stack Γ ns
    {δ} : Sub · Γ
    ins : Is D sΓ d σ σ'
    env : Env D len
    st : Env D ms
    sf : Sf D lf
    wf-env : env ⊨ sΓ as δ
    wf-st : wf-env ⊢ st ⊨ˢ σ
