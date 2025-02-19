module Model.Labels where

open import Agda.Primitive
open import Lib.Basic using (ℕ; zero; suc)
open import Model.Shallow
open import Model.Context

private variable
  i j k i' j' k' : Level
  Γ : Con i
  A : Ty Γ j
  B : Ty (Γ ▹ A) k
  l m n id : ℕ
  sΓ : Ctx Γ l

record LCon : Setω₁ where
  field
    Pi : (id : ℕ) (sΓ : Ctx Γ l) (A : Ty Γ j) (B : Ty (Γ ▹ A) k) → Setω
  --
    interp : (lab : Pi id sΓ A B) → Tm (Γ ▹ A) B
  --
    _⟦_⟧ : 
      {Δ : Con i'} (lab : Pi id sΓ A B) (σ : Sub Δ Γ) → 
      Tm Δ (Π (A [ σ ]T) (B [ σ ^ A ]T))
 