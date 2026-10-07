module SECD.Theorem.Termination where

import Lib.Basic as b
open import Lib.Order
open b using (ℕ)

open import Model.Universe
open import Model.Shallow hiding (↓; ↓!)
open import Model.Context
open import Model.Stack

open import SECD.Syntax
open import SECD.Value
open import SECD.Config
open import SECD.Opsem

open import SECD.Theorem.Halting
open import SECD.Theorem.Fundamental

open b using (_≡_; _×_)

private variable
  m n len ms ns lf : ℕ

{- Well-typed values, environments and stacks halt -}

mutual
  all-H : ∀ {A : Type (b.suc n)}{t : Tm · (λ _ → A)} (v : Val t) → H v
  all-H lit-ttn = tt₁
  all-H (lit-n k) = tt₁
  all-H (ty A) = tt₁
  all-H (clo env ins ⦃ pf ⦄) = H-clo ins pf (all-Hᵉ pf)
  all-H (lift v) = all-H v
  all-H (pair v₁ v₂) = all-H v₁ b., all-H v₂

  all-Hᵉ : ∀ {Γ : Con}{sΓ : Ctx Γ len}{env : Env len}{δ : Sub · Γ}
    (wf : env ⊨ sΓ as δ) → Hᵉ wf
  all-Hᵉ nil = tt₁
  all-Hᵉ (cons {v = v} pf pA) = all-Hᵉ pf b., all-H v

all-Hˢ : ∀ {Γ : Con}{sΓ : Ctx Γ len}{env : Env len}{δ : Sub · Γ}
  {wf : env ⊨ sΓ as δ}{st : Env ns}{σ : Stack Γ ns} →
  (wf-st : wf ⊢ st ⊨ˢ σ) → Hˢ wf-st
all-Hˢ nil = tt₁
all-Hˢ (cons {v = v} pf ptt eq) = all-Hˢ pf b., all-H v

{- Termination at the current frame -}

halts-frame : ∀ (c : Config) → Halts c
halts-frame (conf ins env st sf wf-env wf-st eq-A eq-t) =
  Fund ins wf-env (all-Hᵉ wf-env) wf-st (all-Hˢ wf-st) eq-A eq-t

{- Termination, by induction on the stack of call frames -}

Termination-sf :
  ∀ {Γ : Con}{A : Ty Γ n}{s : Tm Γ A}{η : Sub · Γ} (sf : Sf s η lf) →
  ∀ {Δ : Con}{sΔ : Ctx Δ len}{σ : Stack Δ ms}{σ' : Stack Δ ns}{A' : Ty Δ n}{t' : Tm Δ A'}
    (ins : Is sΔ σ (σ' ∷ t'))
    (env : Env len)(st : Env ms){δ : Sub · Δ}
    (wf-env : env ⊨ sΔ as δ)(wf-st : wf-env ⊢ st ⊨ˢ σ)
    (eq-A : A' [ δ ]T ≡ A [ η ]T)
    (eq-t : s [ η ] ≡ Tm-subst (t' [ δ ]) (b.cong-app eq-A)) →
  conf ins env st sf wf-env wf-st eq-A eq-t ⇓!
Termination-sf (◆ t) ins env st wf-env wf-st eq-A eq-t
  with halts-frame (conf ins env st (◆ t) wf-env wf-st eq-A eq-t)
... | halts v (halt tr) hv = Halt! v (Halt tr)
Termination-sf (sf ∷ fr ins' env' st' wf-env' wf-st' eq-A' eq-t') ins env st wf-env wf-st eq-A eq-t
  with halts-frame (conf ins env st (sf ∷ fr ins' env' st' wf-env' wf-st' eq-A' eq-t') wf-env wf-st eq-A eq-t)
... | halts v (halt {eq-A = eqA} {eq-t = eqt} tr) hv
  with Termination-sf sf ins' env' (st' ∷ v) wf-env' (cons wf-st' (b.cong-app eqA) eqt) eq-A' eq-t'
... | Halt! v' (Halt tr') = Halt! v' (Halt (tr ++* (C-RET ⟫ tr')))

Termination : ∀ (c : Config) → c ⇓!
Termination (conf ins env st sf wf-env wf-st eq-A eq-t) =
  Termination-sf sf ins env st wf-env wf-st eq-A eq-t

{- Total correctness -}

TotalCorrectness :
  ∀ {Δ : Con}{sΔ : Ctx Δ len}{σ : Stack Δ ms}{σ' : Stack Δ ns}{A' : Ty Δ n}{t' : Tm Δ A'}
    (ins : Is sΔ σ (σ' ∷ t'))
    {env : Env len}{st : Env ms}{δ : Sub · Δ}
    (wf-env : env ⊨ sΔ as δ)(wf-st : wf-env ⊢ st ⊨ˢ σ) →
  b.Σ (Val (t' [ δ ]))
      (λ v → conf ins env st (◆ (t' [ δ ])) wf-env wf-st b.refl b.refl ⇓ v)
TotalCorrectness {t' = t'} ins {δ = δ} wf-env wf-st
  with halts-frame (conf ins _ _ (◆ (t' [ δ ])) wf-env wf-st b.refl b.refl)
... | halts v (halt tr) hv = v b., Halt tr

TotalCorrectness-program :
  ∀ {σ : Stack · ns}{A : Ty · n}{t : Tm · A} (ins : Is ◆ ◆ (σ ∷ t)) →
  b.Σ (Val t) (λ v → conf ins ◆ ◆ (◆ t) nil nil b.refl b.refl ⇓ v)
TotalCorrectness-program ins = TotalCorrectness ins nil nil
