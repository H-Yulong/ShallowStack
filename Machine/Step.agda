{-# OPTIONS --safe #-}

module Step where

open import Agda.Primitive
import Basic as lib
open import Shallow
open import Labels
open import Context
open import Stack
open import Theory

open LCon
open Library

-- Machine configuration

data Frame (D : LCon) : Setω where
  fr<_,_,_> : 
    ∀ {i}{Γ : Con i}
      {m}{σ : Stack Γ m}
      {n}{σ' : Stack Γ n}
      {l}{sΓ : Ctx Γ l} → 
      Env D l → Is D sΓ σ σ' → lib.ℕ → Frame D

data Frs (D : LCon) : lib.ℕ → Setω where
  ◆ : Frs D 0
  _∷_ : ∀{n} → Frame D → Frs D n → Frs D (lib.suc n)

-- Goal of this ver.
-- Have just the length requirement encoded, i.e. "well-scoped" extrinsic configs,
-- and have well-formedness proofs as a separate thing,
-- while keeping the well-formedness conditions invariant in the step relation.

record Config (D : LCon) : Setω where
  constructor conf<_,_,_,_>
  field
    {i} : Level
    {Γ} : Con i
    {l m n} : lib.ℕ
    {sΓ} : Ctx Γ l
    {σ} : Stack Γ m
    {σ'} : Stack Γ n
    instr : Is D sΓ σ σ'
    --
    env : Env D l
    --
    st : Env D m
    -- 
    {lf} : lib.ℕ
    frames : Frs D lf
    --

dup : 
  ∀ {D : LCon}
    {i}{Γ : Con i}
    {j}{A : Ty Γ j}
    {m}{σ : Stack Γ m} → 
    Env D m → SVar σ A → Env D (lib.suc m)
dup (env ∷ v) vz = env ∷ v ∷ v
dup (env ∷ v) (vs x) = (dup env x) ∷ v

step-APP : 
  ∀ (L : Library)
    {i}{Γ : Con i}
    {l}{sΓ : Ctx Γ l}
    {j}{A : Ty Γ j}
    {k}{B : Ty (Γ ▹ A) k}
    {i'}{Δ : Con i'}
    {l'}{sΔ : Ctx Δ l'}
    {j'}{A' : Ty Δ j'}
    {k'}{B' : Ty (Δ ▹ A') k'}
    {id}(lab : Pi (D L) id sΔ A' B')
    (env' : Env (D L) l') → 
    ⦃ pf' : sΔ ⊨ env' ⦄ → 
    ∀{f : Tm Γ (Π A B)}{a : Tm Γ A}
    {m}{σ : Stack Γ m}
    {n}{σ' : Stack Γ n}
    (is : Is (D L) sΓ (σ ∷ f $ a) σ')
    (env : Env (D L) l)
    (st : Env (D L) m)
    {lf}(frames : Frs (D L) lf) → 
    ⦃ pf : sΓ ⊨ env ⦄ → 
    {t : Tm · (A [ ⟦ pf ⟧⊨ ]T)}
    (va : Val (D L) t) → 
    Config (D L)
step-APP L lab env' {m = m} {σ = σ} is env st frames va with impl L lab {σ = {!   !}}
... | proc is' = conf< is' , env' ∷ va , st , fr< env , is , m > ∷ frames >

data _⊢_↝_ (L : Library) : Config (D L) → Config (D L) → Setω where
  C-NOP : 
    ∀ {i}{Γ : Con i}
      {l}{sΓ : Ctx Γ l}
      {m}{σ : Stack Γ m}
      {n}{σ' : Stack Γ n}
      {is : Is (D L) sΓ σ σ'}
      {env : Env (D L) l}
      {st : Env (D L) m}
      {lf}{frames : Frs (D L) lf} → 
      L ⊢ conf< NOP >> is , env , st , frames >
        ↝ conf< is , env , st , frames >
  ----
  C-VAR : 
    ∀ {i}{Γ : Con i}
      {l}{sΓ : Ctx Γ l}
      {j}{A : Ty Γ j}{x : V sΓ A}
      {m}{σ : Stack Γ m}
      {n}{σ' : Stack Γ n}
      {is : Is (D L) sΓ (σ ∷ ⟦ x ⟧V) σ'}
      {env : Env (D L) l}
      {st : Env (D L) m}
      {lf}{frames : Frs (D L) lf} → 
      ⦃ pf : sΓ ⊨ env ⦄ → 
        L ⊢ conf< VAR x >> is , env , st , frames > 
          ↝ conf< is , env , st ∷ findᵉ env x , frames >
  ----
  C-ST : 
    ∀ {i}{Γ : Con i}
      {l}{sΓ : Ctx Γ l}
      {j}{A : Ty Γ j}
      {m}{σ : Stack Γ m}
      {n}{σ' : Stack Γ n}
      {x : SVar σ A}
      {is : Is (D L) sΓ (σ ∷ find σ x) σ'}
      {env : Env (D L) l}
      {st : Env (D L) m}
      {lf}{frames : Frs (D L) lf} → 
        L ⊢ conf< ST x >> is , env , st , frames > 
          ↝ conf< is , env , dup st x , frames >
  ----
  C-CLO : 
    ∀ {n : lib.ℕ}
      {i}{Γ : Con i}
      {sl}{sΓ : Ctx Γ sl}
      {m}{σ : Stack Γ (n lib.+ m)}
      {j}{Δ : Con j}{sΔ : Ctx Δ n}
      {k}{A : Ty Δ k}
      {l}{B : Ty (Δ ▹ A) l}
      {x}(lab : Pi (D L) x sΔ A B)
      ⦃ pf : Γ ⊢ (take n σ) of Δ ⦄ → 
      ∀{n'}{σ' : Stack Γ n'}
      {is : Is (D L) sΓ (drop n σ ∷ _⟦_⟧ (D L) lab ⟦ pf ⟧s) σ'}
      {env : Env (D L) sl}
      {st : Env (D L) (n lib.+ m)}
      {lf}{frames : Frs (D L) lf} → 
      ⦃ pfΓ : sΓ ⊨ env ⦄ →
      ⦃ pfΔ : sΔ ⊨ takeᵉ n st ⦄ → 
        L ⊢ conf< CLO n lab >> is , env , st , frames > 
          ↝ conf< is , env , (dropᵉ n st) ∷ clo lab (takeᵉ n st) , frames >
  C-APP : 
    ∀ {i}{Γ : Con i}
      {l}{sΓ : Ctx Γ l}
      {j}{A : Ty Γ j}
      {k}{B : Ty (Γ ▹ A) k}
      {i'}{Δ : Con i'}
      {l'}{sΔ : Ctx Δ l'}
      {j'}{A' : Ty Δ j'}
      {k'}{B' : Ty (Δ ▹ A') k'}
      {id}{lab : Pi (D L) id sΔ A' B'}
      {env' : Env (D L) l'} → 
      ⦃ pf' : sΔ ⊨ env' ⦄ → 
      ∀{f : Tm Γ (Π A B)}{a : Tm Γ A}
      {m}{σ : Stack Γ m}
      {n}{σ' : Stack Γ n}
      {is : Is (D L) sΓ (σ ∷ f $ a) σ'}
      {env : Env (D L) l}
      {st : Env (D L) m}
      {lf}{frames : Frs (D L) lf} → 
      ⦃ pf : sΓ ⊨ env ⦄ → 
      {t : Tm · (A [ ⟦ pf ⟧⊨ ]T)}
      {va : Val (D L) t} → 
      L ⊢ conf< APP {f = f} {a = a} >> is , env , st ∷ clo lab env' ∷ va , frames > 
        ↝ step-APP L lab env' {f = f} is env st frames va



    