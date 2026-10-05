module DAM.Labels where

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
open LCon public

lapp : 
    ∀ (D : LCon){Δ : Con}{A : Ty Γ n}{B : Ty (Γ ▹ A) n} → 
      (L : Pi D id sΓ A B) → 
      (σ : Sub Δ Γ) → 
    ------------------------------------
    Tm Δ (Π (A [ σ ]T) (B [ σ ^ A ]T))
lapp D L σ = ~λ (λ γ α → (interp D L) ~$ (σ γ ~, α))

lapp[] : 
  ∀ {D}{Δ Θ}{sΓ : Ctx Γ len}{A : Ty Γ n}{B : Ty (Γ ▹ A) n}
    {L : Pi D id sΓ A B}{σ : Sub Δ Γ}{δ : Sub Θ Δ} → 
  ((lapp D L σ) [ δ ]) ≡ lapp D L (σ ∘ δ)
lapp[] = _≡_.refl

lapp-β : 
  ∀ {D}{Δ}{A : Ty Γ n}{B : Ty (Γ ▹ A) n} → 
    {L : Pi D id sΓ A B} → 
    {σ : Sub Δ Γ} → 
    {t : Tm Δ (A [ σ ]T)} →
  (lapp D L σ) $ t ≡ (interp D L) [ σ ▻ t ]
lapp-β = _≡_.refl
