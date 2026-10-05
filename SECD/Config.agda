module SECD.Config where

import Lib.Basic as b
open import Lib.Order

open import Model.Universe
open import Model.Shallow
open import Model.Context
open import Model.Stack
open import SECD.Syntax

open import SECD.Value

open b using (ℕ; _+_; _≡_)

-- Machine configuration

-- Call frame
record Frame {n : ℕ} {Γ : Con} {A : Ty Γ n} (s : Tm Γ A) (η : Sub · Γ) : Set₁ where
  constructor fr
  field
    {len ms ns m} : ℕ
    {Δ} : Con
    {sΔ} : Ctx Δ len
    {σ} : Stack Δ ms
    {σ'} : Stack Δ ns
    {B} : Ty Δ m
    {t} : Tm Δ B
    {A'} : Ty Δ n
    {t'} : Tm Δ A'
    ----
    ins : Is sΔ (σ ∷ t) (σ' ∷ t')
    env : Env len
    st : Env ms
    ----
    {δ} : Sub · Δ
    wf-env : env ⊨ sΔ as δ
    wf-st : wf-env ⊢ st ⊨ˢ σ
    eq-A : A' [ δ ]T ≡ A [ η ]T
    eq-t : s [ η ] ≡ Tm-subst (t' [ δ ]) (b.cong-app eq-A)


-- Stack of frames
data Sf : ∀{n}{Γ : Con}{A : Ty Γ n} → Tm Γ A → Sub · Γ → ℕ → Set₁ where
  ◆ : ∀{n}{A : Type (b.suc n)} → (t : Tm · (λ _ → A)) → Sf t ε 0
  ----
  _∷_ :
    ∀ {m n}{Γ : Con}{A : Ty Γ n}
      {s : Tm Γ A}{δ : Sub · Γ} →
      Sf s δ m →
      (frame : Frame s δ) →
      Sf (Frame.t frame) (Frame.δ frame) (b.suc m)

{-
  Machine configuration:
    - [ins] : Instruction sequence
    - [env] : Environment values
    - [st]  : Stack of values
    - [sf]  : Stack of call frames

  Parameters:
    - [Δ, σ, σ', t', δ] : Abstract type parameters, such that
      - Δ ⊢ ins : σ → σ' ∷ t'        (Instruction well-typed)
      - [wf-env] : env ⊨ Δ as δ      (Env realizes context, δ for env)
      - [wf-st] : wf-env ⊢ st ⊨ˢ σ   (Stack realizes abstract stack)

    - [Γ, A, s, η] : The return expected by the top call frame, such that
      - [eq-A] : A' [ δ ]T ≡ A [ η ]T   (Return types compatible)
      - [eq-t] : s [ η ] ≡ t' [ δ ]     (Return terms compatible)

    - [len, ms, ns, lf] : Lengths
-}

record Config : Set₁ where
  constructor conf
  field
    {len ms ns n lf} : ℕ
    {Γ Δ} : Con
    {sΔ} : Ctx Δ len
    {σ} : Stack Δ ms
    {σ'} : Stack Δ ns
    {A} : Ty Γ n
    {s} : Tm Γ A
    {η} : Sub · Γ
    {A'} : Ty Δ n
    {t'} : Tm Δ A'
    ----
    ins : Is sΔ σ (σ' ∷ t')
    env : Env len
    st : Env ms
    ----
    sf : Sf s η lf
    ----
    {δ} : Sub · Δ
    wf-env : env ⊨ sΔ as δ
    wf-st : wf-env ⊢ st ⊨ˢ σ
    eq-A : A' [ δ ]T ≡ A [ η ]T
    eq-t : s [ η ] ≡ Tm-subst (t' [ δ ]) (b.cong-app eq-A)
