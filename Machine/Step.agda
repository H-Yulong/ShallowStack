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

-- Helper functions

-- dup : 
--   ∀ {D : LCon}
--     {i}{Γ : Con i}
--     {n}{σ : Stack Γ n}
--     {j}{A : Ty Γ j} → 
--     Env D n → SVar σ A → Env D (lib.suc n)
-- dup (env ∷ t) vz = env ∷ t ∷ t
-- dup (env ∷ t) (vs x) = (dup env x) ∷ t

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
