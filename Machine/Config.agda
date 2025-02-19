module Machine.Config where

open import Agda.Primitive
import Lib.Basic as lib

open import Model.Shallow
open import Model.Context
open import Model.Labels
open import Model.Stack

open import Machine.Value

open lib using (ℕ; _+_; _≤_)
open LCon

-- Machine configuration

-- Call frame
record Frame (D : LCon) : Setω where
  constructor fr
  field
    {i} : Level
    {l m n} : ℕ
    {Γ} : Con i
    {sΓ} : Ctx Γ l
    {σ} : Stack Γ m
    {σ'} : Stack Γ n
    ins : Is D sΓ σ σ'
    env : Env D l
    len : ℕ

-- Stack of frames
data Sf (D : LCon) : ℕ → Setω where
  ◆ : Sf D 0
  _∷_ : ∀{n} → Sf D n → Frame D → Sf D (lib.suc n)

-- Machine state: env, stack, and frame stack
record Config (D : LCon) : Setω where
  constructor conf
  field
    {i} : Level
    {l m n s lf} : ℕ
    {Γ} : Con i
    {sΓ} : Ctx Γ l
    {σ} : Stack Γ m
    {σ'} : Stack Γ n
    ins : Is D sΓ σ σ'
    env : Env D l
    st : Env D (m + s)
    sf : Sf D lf

record VConfig (D : LCon) : Setω where
  constructor vconf
  field
    -- Raw configuration
    cf : Config D
    -- Runtime environment env implements Γ
    wf-env : Config.sΓ cf ⊨ Config.env cf
    -- Runtime stack st implements σ, w.r.t. the runtime environment
    wf-st : wf-env ⊢ Config.σ cf ⊨ˢ takeᵉ (Config.m cf) (Config.st cf)

-- data _↝_ {D : LCon} : Config D → Config D → Setω where
--   C-NOP : 
--     ∀ {i}{Γ : Con i}
--       {l}{sΓ : Ctx Γ l}
--       {m}{σ : Stack Γ m}
--       {n}{σ' : Stack Γ n}
--       {is : Is D sΓ σ σ'}
--       {env : Env D l}
--       {st : Env D m}
--       {lf}{frames : Frames D lf} → 
--       ⦃ pf : sΓ ⊨ env ⦄ → 
--         conf< NOP >> is , env , st , frames > ↝ conf< is , env , st , frames >
--   ----
--   C-VAR : 
--     ∀ {i}{Γ : Con i}
--       {l}{sΓ : Ctx Γ l}
--       {j}{A : Ty Γ j}{x : V sΓ A}
--       {m}{σ : Stack Γ m}
--       {n}{σ' : Stack Γ n}
--       {is : Is D sΓ (σ ∷ ⟦ x ⟧V) σ'}
--       {env : Env D l}
--       {st : Env D m}
--       {lf}{frames : Frames D lf} → 
--       ⦃ pf : sΓ ⊨ env ⦄ → 
--         conf< VAR x >> is , env , st , frames > ↝ conf< is , env , st ∷ findᵉ env x , frames >
--   ----
--   C-ST : 
--     ∀ {i}{Γ : Con i}
--       {l}{sΓ : Ctx Γ l}
--       {j}{A : Ty Γ j}
--       {m}{σ : Stack Γ m}
--       {n}{σ' : Stack Γ n}
--       {x : SVar σ A}
--       {is : Is D sΓ (σ ∷ find σ x) σ'}
--       {env : Env D l}
--       {st : Env D m}
--       {lf}{frames : Frames D lf} → 
--       ⦃ pf : sΓ ⊨ env ⦄ →
--         conf< ST x >> is , env , st , frames > ↝ conf< is , env , dup st x , frames >
--   ----
--   C-CLO : 
--     ∀ {n : lib.ℕ}
--       {i}{Γ : Con i}
--       {sl}{sΓ : Ctx Γ sl}
--       {m}{σ : Stack Γ (n lib.+ m)}
--       {j}{Δ : Con j}{sΔ : Ctx Δ n}
--       {k}{A : Ty Δ k}
--       {l}{B : Ty (Δ ▹ A) l}
--       {x}(L : Pi D x sΔ A B)
--       {{pf : Γ ⊢ (take n σ) of Δ}} → 
--       ∀{n'}{σ' : Stack Γ n'}
--       {is : Is D sΓ (drop n σ ∷ _⟦_⟧ D L ⟦ pf ⟧s) σ'}
--       {env : Env D sl}
--       {st : Env D (n lib.+ m)}
--       {lf}{frames : Frames D lf} → 
--       ⦃ pf : sΓ ⊨ env ⦄ →
--         conf< CLO n L >> is , env , st , frames > ↝ conf< is , env , {!   !} ∷ {!   !} , frames >


-- {-
--     CLO : 
--       ∀(n : lib.ℕ)
--       {m}{σ : Stack Γ (n lib.+ m)}
--       {j}{Δ : Con j}{sΔ : Ctx Δ n}
--       {k}{A : Ty Δ k}
--       {l}{B : Ty (Δ ▹ A) l}
--       {x}(L : Pi D x sΔ A B)
--       {{pf : Γ ⊢ (take n σ) of Δ}} → 
--       Instr D sΓ σ (drop n σ ∷ _⟦_⟧ D L ⟦ pf ⟧s)
-- -}
