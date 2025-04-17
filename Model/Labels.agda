module Model.Labels where

open import Agda.Primitive
open import Lib.Basic using (ℕ; zero; suc; _≡_)
open import Model.Shallow
open import Model.Context

private variable
  n m id : ℕ
  Γ : Con
  A : Ty Γ n
  B : Ty (Γ ▹ A) m
  sΓ : Ctx Γ l

record LCon : Setω₁ where
  field
    Pi : (id : ℕ) (sΓ : Ctx Γ l) (A : Ty Γ j) (B : Ty (Γ ▹ A) k) → Setω
  --
    interp : (lab : Pi id sΓ A B) → Tm (Γ ▹ A) B
  --
    lapp : 
      {Δ : Con i'} (lab : Pi id sΓ A B) (σ : Sub Δ Γ) → 
      Tm Δ (Π (A [ σ ]T) (B [ σ ^ A ]T))
  --
    lapp[] : 
      {Δ : Con i'} {Γ' : Con j'} 
      {L : Pi id sΓ A B} {σ : Sub Δ Γ} {δ : Sub Γ' Δ} → 
      ((lapp L σ) [ δ ]) ≡ lapp L (σ ∘ δ)
