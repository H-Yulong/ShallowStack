module Machine.Config where

import Lib.Basic as b
open import Lib.Order

open import Model.Universe
open import Model.Shallow
open import Model.Context
open import Model.Labels
open import Model.Stack

open import Machine.Value

open b using (ℕ; _+_; _≡_)

-- Machine configuration

-- Call frame 
record Frame (D : LCon) {n : ℕ} {Γ : Con} {A : Ty Γ n} (s : Tm Γ A) (η : Sub · Γ) : Set₁ where
  constructor fr
  field
    {len ms ns m d} : ℕ
    {Δ} : Con
    {sΔ} : Ctx Δ len
    {σ} : Stack Δ ms
    {σ'} : Stack Δ ns
    {B} : Ty Δ m
    {t} : Tm Δ B
    {A'} : Ty Δ n
    {t'} : Tm Δ A'
    ----
    ins : Is D sΔ d (σ ∷ t) (σ' ∷ t')
    env : Env D len
    st : Env D ms
    ----
    {δ} : Sub · Δ
    wf-env : env ⊨ sΔ as δ
    wf-st : wf-env ⊢ st ⊨ˢ σ
    eq-A : A' [ δ ]T ≡ A [ η ]T
    eq-t : s [ η ] ≡ Tm-subst (t' [ δ ]) (b.cong-app eq-A) 


-- Stack of frames
data Sf (D : LCon) : ∀{n}{Γ : Con}{A : Ty Γ n} → Tm Γ A → Sub · Γ → ℕ → Set₁ where
  ◆ : ∀{n}{A : Type (b.suc n)}{t : Tm · (λ _ → A)} → (v : Val D t) → Sf D t ε 0
  ----
  _∷_ : 
    ∀ {m n}{Γ : Con}{A : Ty Γ n}
      {s : Tm Γ A}{δ : Sub · Γ} →
      Sf D s δ m →
      (frame : Frame D s δ) → 
      Sf D (Frame.t frame) (Frame.δ frame) (b.suc m)

{- 
  Machine configuration: 
    - [ins] : Instruction sequence
    - [env] : Environment values
    - [st]  : Stack of values
    - [sf]  : Stack of call frames

  Parameters:
    - [Γ, σ, σ', t, η] : Abstract type parameters, such that
      - Γ ⊢ ins : σ → σ' ∷ t          (Instruction well-typed)
      - [wf-env] : env ⊨ Γ as η      (Env realizes context, η for env)
      - [wf-st] : wf-env ⊢ st ⊨ˢ σ   (Stack realizes abstract stack)

    - [??] : Function call parameters, such that
      - ??
    
    - [len, ms, ns, lf, d] : Lengths and termination marker

-}

record Config (D : LCon) : Set₁ where
  constructor conf
  field
    {len ms ns m n lf d} : ℕ
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
    ins : Is D sΔ d σ (σ' ∷ t')
    env : Env D len
    st : Env D ms
    ----
    sf : Sf D s η lf
    ----
    {δ} : Sub · Δ
    wf-env : env ⊨ sΔ as δ
    wf-st : wf-env ⊢ st ⊨ˢ σ
    eq-A : A' [ δ ]T ≡ A [ η ]T
    eq-t : s [ η ] ≡ Tm-subst (t' [ δ ]) (b.cong-app eq-A) 
