{-# OPTIONS --safe #-}

module Labels where

open import Agda.Primitive
import Basic as lib
open import Shallow
open import Context

record LCon : Setω where
  field
    Pi : 
      ∀(id : lib.ℕ)
       {i}{Γ : Con i}
       {n}(sΓ : Ctx Γ n)
       {j}(A : Ty Γ j)
       {k}(B : Ty (Γ ▹ A) k) → Set
  ----
    interp : 
      ∀{id : lib.ℕ}
      {i}{Γ : Con i}
      {n}{sΓ : Ctx Γ n}
      {j}{A : Ty Γ j}
      {k}{B : Ty (Γ ▹ A) k} →
      Pi id sΓ A B → Tm (Γ ▹ A) B
  ----
    _⟦_⟧ : 
      ∀{id : lib.ℕ}
      {i}{Γ : Con i}
      {n}{sΓ : Ctx Γ n}
      {j}{A : Ty Γ j}
      {k}{B : Ty (Γ ▹ A) k}
      {l}{Δ : Con l} → 
      Pi id sΓ A B → (σ : Sub Δ Γ) → 
      Tm Δ (Π (A [ σ ]T) (B [ σ ^ A ]T))
