module Machine.Config where

open import Agda.Primitive
import Lib.Basic as lib

open import Model.Shallow
open import Model.Context
open import Model.Labels
open import Model.Stack

open import Machine.Value

open lib using (ℕ; _+_)
open LCon

-- Machine configuration

-- Call frame
record Frame (D : LCon) : Setω where
  constructor fr
  field
    {i} : Level
    {l m n d} : ℕ
    {Γ} : Con i
    {sΓ} : Ctx Γ l
    {σ} : Stack Γ m
    {σ'} : Stack Γ n
    ins : Is D sΓ d σ σ'
    env : Env D l
    len : ℕ

-- Stack of frames
data Sf (D : LCon) : ℕ → Setω where
  ◆ : Sf D 0
  _∷_ : ∀{n} → Sf D n → Frame D → Sf D (lib.suc n)

-- Machine state: instr, env, stack, and frame stack
record Config (D : LCon) : Setω where
  constructor conf
  field
    {i} : Level
    {l m n s lf d} : ℕ
    {Γ} : Con i
    {sΓ} : Ctx Γ l
    {σ} : Stack Γ m
    {σ'} : Stack Γ n
    ins : Is D sΓ d σ σ'
    env : Env D l
    st : Env D (m + s)
    sf : Sf D lf

-- Well-formed configuration
record VConfig (D : LCon) (cf : Config D): Setω where
  constructor vconf
  field
    -- Runtime environment env implements Γ
    wf-env : Config.sΓ cf ⊨ Config.env cf
    -- Runtime stack st implements σ, w.r.t. the runtime environment
    wf-st : wf-env ⊢ Config.σ cf ⊨ˢ takeᵉ (Config.m cf) (Config.st cf)

