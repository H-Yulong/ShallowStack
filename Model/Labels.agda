module Model.Labels where

open import Agda.Primitive
open import Lib.Basic using (ℕ; zero; suc; _≡_)
open import Lib.Order

open import Model.Universe
open import Model.Shallow
open import Model.Context

private variable
  Γ : Con
  len n id : ℕ
  sΓ : Ctx Γ len

record LCon : Set₂ where
  field
    Pi : (id : ℕ) (sΓ : Ctx Γ len) (A : Ty Γ n) (B : Ty (Γ ▹ A) n) → Set₁
  --
    interp : ∀{A : Ty Γ n}{B : Ty (Γ ▹ A) n} → (L : Pi id sΓ A B) → Tm (Γ ▹ A) B
  --
    lapp : 
        ∀   {Δ}{A : Ty Γ n}{B : Ty (Γ ▹ A) n} → 
          (L : Pi id sΓ A B) → 
          (σ : Sub Δ Γ) → 
        ------------------------------------
        Tm Δ (Π (A [ σ ]T) (B [ σ ^ A ]T))
  --
    lapp[] : 
      ∀ {Δ Θ}{A : Ty Γ n}{B : Ty (Γ ▹ A) n}
        {L : Pi id sΓ A B}{σ : Sub Δ Γ}{δ : Sub Θ Δ} → 
      ((lapp L σ) [ δ ]) ≡ lapp L (σ ∘ δ)
  --
    lapp-β : 
      ∀ {Δ}{A : Ty Γ n}{B : Ty (Γ ▹ A) n} → 
        {L : Pi id sΓ A B} → 
        {σ : Sub Δ Γ} → 
        {t : Tm Δ (A [ σ ]T)} →
      (lapp L σ) $ t ≡ (interp L) [ σ ▻ t ]
