{-# OPTIONS --safe #-}

module Config where

open import Agda.Primitive
import Basic as lib
open import Shallow
open import Labels
open import Context
open import Stack
open import Theory

open LCon

-- Machine configuration
data Fr (D : LCon) : Setω where
  fr<_,_> : ∀{n} → Env D n → lib.ℕ → Fr D

data Frames (D : LCon) : lib.ℕ → Setω where
  ◆ : Frames D 0
  _∷_ : ∀{n} → Fr D → Frames D n → Frames D (lib.suc n)

-- Need to remake this...
-- Design: Config is just < stack, env, frames >
-- Then, have a datatype saying that "c is a valid config for running instr",
-- which has these conditions (where instr : Is D sΓ σ σ')
--    - stack, env, frames have the same D
--    - env implements sΓ
--    - stack implements σ (need new judgement for this)
-- That's saying we have a "well-formed config",
-- and the machine steps through well-formed configs only.

record Config (D : LCon) : Setω where
  constructor conf<_,_,_,_>
  field
    k : lib.Bool

data _↝_ {D : LCon} : Config D → Config D → Setω where
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
