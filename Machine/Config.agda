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
record Frame (D : LCon) {Δ : Con} (δ' : Sub · Δ) : Set₁ where
  constructor fr
  field
    {len ms ns n d} : ℕ
    {Γ} : Con
    {sΓ} : Ctx Γ len
    {A} : Ty Γ n
    {t} : Tm Γ A
    {δ} : Sub · Γ
    {σ} : Stack Γ ms
    {σ'} : Stack Γ ns
    ins : Is D sΓ d (σ ∷ t) σ'
    env : Env D len
    st  : Env D ms
    wf-env : env ⊨ sΓ as δ
    wf-st : wf-env ⊢ st ⊨ˢ σ
    ----
    η : Sub Δ Γ
    call-compat : δ b.≡ η ∘ δ'


-- Stack of frames
data Sf (D : LCon) : {Γ : Con} → Sub · Γ → ℕ → Set₁ where
  ◆ : Sf D ε 0
  _∷_ : 
    ∀ {Δ n}{δ' : Sub · Δ} → 
      Sf D δ' n → 
      (frame : Frame D δ') →  
    Sf D (Frame.δ frame) (b.suc n)

-- caller-ctx : ∀{D lf} → Sf D lf → Con
-- caller-ctx ◆ = ·
-- caller-ctx (sf ∷ frame) = Frame.Γ frame

-- caller-sub : ∀{D lf} → (sf : Sf D lf) → Sub · (caller-ctx sf)
-- caller-sub ◆ = ε
-- caller-sub (sf ∷ frame) = Frame.δ frame

-- Machine state: instr, env, stack, and frame stack
record Config (D : LCon) : Set₁ where
  constructor conf
  field
    {len ms ns lf d} : ℕ
    {Γ Δ} : Con
    {sΓ} : Ctx Γ len
    {σ} : Stack Γ ms
    {σ'} : Stack Γ ns
    {δ} : Sub · Γ
    {δ'} : Sub · Δ
    ins : Is D sΓ d σ σ'
    env : Env D len
    st : Env D ms
    sf : Sf D δ' lf
    --
    wf-env : env ⊨ sΓ as δ
    wf-st : wf-env ⊢ st ⊨ˢ σ
    --
    η : Sub Δ Γ 
    call-compat : δ b.≡ η ∘ δ'

