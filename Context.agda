{-# OPTIONS --safe #-}

module Context where

open import Agda.Primitive
open import Basic using (ℕ; zero; suc)
open import Shallow hiding (zero; suc)

infixl 5 _∷_

-- Deeper shallow embedded context,
-- useful for accessing runtime environments

data Ctx : ∀{i} → Con i → ℕ → Setω where
  ◆ : Ctx · 0
  _∷_ : 
    ∀ {i}{Γ : Con i}{j}{n} → 
      Ctx Γ n → (A : Ty Γ j) → Ctx (Γ ▹ A) (suc n)

-- Literal variables, essentially Fin
data V : 
  ∀ {i}{Γ : Con i}
    {n}(sΓ : Ctx Γ n)
    {j}(A : Ty Γ j) → Setω where
  ----
  vz : 
    ∀ {i}{Γ : Con i}
      {n}{sΓ : Ctx Γ n}
      {j}{A : Ty Γ j} → 
      V (sΓ ∷ A) (A [ p ]T) 
  ----
  vs : 
    ∀ {i}{Γ : Con i}
      {n}{sΓ : Ctx Γ n}
      {j}{A : Ty Γ j}
      {k}{B : Ty Γ k} → 
      V sΓ A → V (sΓ ∷ B) (A [ p ]T) 

⟦_⟧V : 
  ∀ {i}{Γ : Con i}
    {j}{A : Ty Γ j}
    {n}{sΓ : Ctx Γ n} → 
    V sΓ A → Var Γ A 
⟦ vz ⟧V = 𝟘
⟦ vs v ⟧V = 𝕤 ⟦ v ⟧V

-- useful names

V₀ : 
  ∀ {i}{Γ : Con i}
    {j}{A : Ty Γ j}
    {n}{sΓ : Ctx Γ n} → 
    V (sΓ ∷ A) (A [ p ]T)
V₀ = vz

V₁ : 
  ∀ {i}{Γ : Con i}
    {j}{A : Ty Γ j}
    {k}{B : Ty (Γ ▹ A) k}
    {n}{sΓ : Ctx Γ n} → 
    V (sΓ ∷ A ∷ B) (A [ p² ]T)
V₁ = vs vz

V₂ : 
  ∀ {i}{Γ : Con i}
    {j}{A : Ty Γ j}
    {k}{B : Ty (Γ ▹ A) k}
    {l}{C : Ty (Γ ▹ A ▹ B) l}
    {n}{sΓ : Ctx Γ n} → 
    V (sΓ ∷ A ∷ B ∷ C) (A [ p³ ]T)
V₂ = vs (vs vz)

V₃ : 
  ∀ {i}{Γ : Con i}
    {j}{A : Ty Γ j}
    {k}{B : Ty (Γ ▹ A) k}
    {l}{C : Ty (Γ ▹ A ▹ B) l}
    {m}{D : Ty (Γ ▹ A ▹ B ▹ C) m}
    {n}{sΓ : Ctx Γ n} → 
    V (sΓ ∷ A ∷ B ∷ C ∷ D) (A [ p⁴ ]T)
V₃ = vs (vs (vs vz))
