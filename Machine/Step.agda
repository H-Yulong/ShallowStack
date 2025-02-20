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

-- Helper functions

dup : {D : LCon}{σ : Stack Γ n} → Env D n → SVar σ A → Env D (lib.suc n)
dup (env ∷ t) vz = env ∷ t ∷ t
dup (env ∷ t) (vs x) = (dup env x) ∷ t

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
      {wf-env : sΓ ⊨ env}
      {wf-st : wf-env ⊢ σ ⊨ˢ takeᵉ m st} →
    ---------------------------------------- 
    I ⊢ (conf ins env st sf wf-env wf-st)
      ↝ (conf ins env st sf wf-env wf-st)
  --
  C-VAR : 
      {x : V sΓ A}
      {σ : Stack Γ m}
      {σ' : Stack Γ n}
      {ins : Is D sΓ d (σ ∷ ⟦ x ⟧V) σ'}
      {env : Env D l}
      {st : Env D (m + s)}
      {sf : Sf D lf} → 
      {wf-env : sΓ ⊨ env}
      {wf-st : wf-env ⊢ σ ⊨ˢ takeᵉ m st} →  
    ----------------------------
    I ⊢ (conf (VAR x >> ins) env st sf wf-env wf-st) 
      ↝ (conf ins env (st ∷ findᵉ env x wf-env) sf wf-env (cons wf-st (lib.ext-⊤ lib.refl)))
  --
  -- C-ST : 
  --     {σ : Stack Γ m}
  --     {σ' : Stack Γ n}
  --     {x : SVar σ A}
  --     {ins : Is D sΓ d (σ ∷ find σ x) σ'}
  --     {env : Env D l}
  --     {st : Env D (m + s)}
  --     {sf : Sf D lf} → 
  --     {wf-env : sΓ ⊨ env}
  --     {wf-st : wf-env ⊢ σ ⊨ˢ takeᵉ m st} →  
  --     --------------------------------------
  --     I ⊢ (conf (ST x >> ins) env st sf wf-env wf-st) 
  --       ↝ conf ins env ({! dup st   !}) sf wf-env (cons wf-st {!   !})

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
