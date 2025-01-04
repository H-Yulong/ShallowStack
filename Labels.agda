{-# OPTIONS --safe #-}

module Labels where

open import Agda.Primitive
import Basic as lib
open import Shallow

import ShallowDFC as D

record LCon : Setω where
  field
    Pi : 
      ∀(n : lib.ℕ)
       {i}(Γ : Con i)
       {j}(A : Ty Γ j)
       {k}(B : Ty (Γ ▹ A) k) → Set
  ----
    _⟦_⟧ : 
      ∀{n : lib.ℕ}
      {i}{Γ : Con i}
      {j}{A : Ty Γ j}
      {k}{B : Ty (Γ ▹ A) k}
      {l}{Δ : Con l} → 
      Pi n Γ A B → (σ : Sub Δ Γ) → 
      Tm Δ (Π (A [ σ ]T) (B [ σ ^ A ]T))
open LCon

instance
  D1 : LCon
  D1 = record { Pi = D.Pi ; _⟦_⟧ = D._⟦_⟧ } 
