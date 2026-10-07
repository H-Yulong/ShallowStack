open import DAM.Labels
open import DAM.Syntax
open import DAM.Theorem.Halting

module DAM.Theorem.Termination {D : LCon} (I : Impl D) where

import Lib.Basic as b
open import Lib.Order
open LCon
open b using (ℕ)

open import Model.Universe
open import Model.Shallow
open import Model.Context
open import Model.Stack

open import DAM.Value
open import DAM.Config
open import DAM.Opsem
open import DAM.Theorem.Halting
open Halting I
open import DAM.Theorem.Fundamental I

open b using (_≡_; _×_)

private variable
  m n len ms ns lf id : ℕ

H-Is-below : 
  ∀ {Γ : Con}{sΓ : Ctx Γ len}{σ : Stack Γ ms}{σ' : Stack Γ ns} → 
    (ins : Is D sΓ σ σ') → 
    (∀ {id Γ len n}{sΓ : Ctx Γ len}{A : Ty Γ n}{B : Ty (Γ ▹ A) n} (L : Pi D id sΓ A B) → id < (#id ins) → H-Pi L) → 
  H-Is ins
H-Is-below RET f = b.tt
H-Is-below (CLO ns L >> ins) f = 
  f L (<⊔n-suc-L {y = #id ins}) b., H-Is-below ins ((λ L' lt' → f L' (<⊔n-R lt')))
H-Is-below (CLOENV L >> ins) f = 
  f L (<⊔n-suc-L {y = #id ins}) b., H-Is-below ins ((λ L' lt' → f L' (<⊔n-R lt')))
H-Is-below (ITER {id = id} {id' = id'} P Z S >> ins) f = 
  f Z (<⊔n-L {z = #id ins} (<⊔n-suc-L {id} {b.suc id'})) b., 
  f S (<⊔n-L {z = #id ins} (<⊔n-suc-R {id'} {b.suc id})) b.,
   H-Is-below ins ((λ L' lt' → f L' (<⊔n-R lt')))
H-Is-below (NOP >> ins) f = H-Is-below ins f
H-Is-below (VAR x >> ins) f = H-Is-below ins f
H-Is-below (POP >> ins) f = H-Is-below ins f
H-Is-below (APP >> ins) f = H-Is-below ins f
H-Is-below (LIT n >> ins) f = H-Is-below ins f
H-Is-below (TY A >> ins) f = H-Is-below ins f
H-Is-below (SWP >> ins) f = H-Is-below ins f
H-Is-below (ST x >> ins) f = H-Is-below ins f
H-Is-below (INC >> ins) f = H-Is-below ins f
H-Is-below (UNIT >> ins) f = H-Is-below ins f
H-Is-below (PAIR >> ins) f = H-Is-below ins f
H-Is-below (FST >> ins) f = H-Is-below ins f
H-Is-below (SND >> ins) f = H-Is-below ins f
H-Is-below (UP >> ins) f = H-Is-below ins f
H-Is-below (DOWN >> ins) f = H-Is-below ins f

all-H-Piₖ : 
  ∀ {id Γ len n}{sΓ : Ctx Γ len}{A : Ty Γ n}{B : Ty (Γ ▹ A) n} → 
    (k : ℕ) → (L : Pi D id sΓ A B) → id < k → H-Pi L
all-H-Piₖ ℕ.zero L ()
all-H-Piₖ{id = id} (b.suc k) L lt wf-env hᵉ v pA hv sf eq-A eq-t = 
  Fund (Proc.instr (I L)) 
    -- H-Is-below ins f
    (H-Is-below (Proc.instr (I L)) (λ {id = id'} L' lt' → all-H-Piₖ k L' (<-pred (<-pred lt' (Proc.wf (I L))) lt)))
    (cons wf-env pA) (hᵉ b., H-unsubst pA hv) nil b.tt eq-A eq-t

all-H-Pi :
  ∀ {id Γ len n}{sΓ : Ctx Γ len}{A : Ty Γ n}{B : Ty (Γ ▹ A) n}
  (L : Pi D id sΓ A B) → H-Pi L
all-H-Pi {id = id} L = all-H-Piₖ (b.suc id) L n<suc

mutual
  all-H : ∀ {A : Type (b.suc n)}{t : Tm · (λ _ → A)} (v : Val D t) → H v
  all-H lit-⊤ = b.tt
  all-H (lit-n k) = b.tt
  all-H (ty A) = b.tt
  all-H (clo L env ⦃ pf ⦄) = all-H-Pi L pf (all-Hᵉ pf)
  all-H (lift v) = all-H v
  all-H (pair v₁ v₂) = all-H v₁ b., all-H v₂

  all-Hᵉ : ∀ {Γ : Con}{sΓ : Ctx Γ len}{env : Env D len}{δ : Sub · Γ}
    (wf : env ⊨ sΓ as δ) → Hᵉ wf
  all-Hᵉ nil = b.tt
  all-Hᵉ (cons {v = v} pf pA) = all-Hᵉ pf b., all-H v

all-Hˢ : ∀ {Γ : Con}{sΓ : Ctx Γ len}{env : Env D len}{δ : Sub · Γ}
  {wf : env ⊨ sΓ as δ}{st : Env D ns}{σ : Stack Γ ns} →
  (wf-st : wf ⊢ st ⊨ˢ σ) → Hˢ wf-st
all-Hˢ nil = b.tt
all-Hˢ (cons {v = v} pf ptt eq) = all-Hˢ pf b., all-H v

{- Termination at the current frame (Lemma "Termination at current frame") -}

halts-frame : ∀ (c : Config D) → Halts c
halts-frame (conf ins env st sf wf-env wf-st eq-A eq-t) =
  Fund ins (H-Pi⇒H-Is all-H-Pi ins) wf-env (all-Hᵉ wf-env) wf-st (all-Hˢ wf-st) eq-A eq-t

{- Termination (Theorem "Termination"), by induction on the stack of call frames -}

Termination-sf :
  ∀ {Γ : Con}{A : Ty Γ n}{s : Tm Γ A}{η : Sub · Γ} (sf : Sf D s η lf) →
  ∀ {Δ : Con}{sΔ : Ctx Δ len}{σ : Stack Δ ms}{σ' : Stack Δ ns}{A' : Ty Δ n}{t' : Tm Δ A'}
    (ins : Is D sΔ σ (σ' ∷ t'))
    (env : Env D len)(st : Env D ms){δ : Sub · Δ}
    (wf-env : env ⊨ sΔ as δ)(wf-st : wf-env ⊢ st ⊨ˢ σ)
    (eq-A : A' [ δ ]T ≡ A [ η ]T)
    (eq-t : s [ η ] ≡ Tm-subst (t' [ δ ]) (b.cong-app eq-A)) →
  I ⊢ conf ins env st sf wf-env wf-st eq-A eq-t ⇓!
Termination-sf (◆ t) ins env st wf-env wf-st eq-A eq-t
  with halts-frame (conf ins env st (◆ t) wf-env wf-st eq-A eq-t)
... | halts v (halt tr) hv = Halt! v (Halt tr)
Termination-sf (sf ∷ fr ins' env' st' wf-env' wf-st' eq-A' eq-t') ins env st wf-env wf-st eq-A eq-t
  with halts-frame (conf ins env st (sf ∷ fr ins' env' st' wf-env' wf-st' eq-A' eq-t') wf-env wf-st eq-A eq-t)
... | halts v (halt {eq-A = eqA} {eq-t = eqt} tr) hv
  with Termination-sf sf ins' env' (st' ∷ v) wf-env' (cons wf-st' (b.cong-app eqA) eqt) eq-A' eq-t'
... | Halt! v' (Halt tr') = Halt! v' (Halt (tr ++* (C-RET ⟫ tr')))

Termination : ∀ (c : Config D) → I ⊢ c ⇓!
Termination (conf ins env st sf wf-env wf-st eq-A eq-t) =
  Termination-sf sf ins env st wf-env wf-st eq-A eq-t

{- Total correctness (Corollary "Total correctness") -}

-- A well-typed instruction sequence, run in an environment and stack
-- implementing its context and initial abstract stack, halts with a
-- value implementing the final abstract term closed by the environment.
-- (The type of the value, Val D (t' [ δ ]), is the correctness statement.)
TotalCorrectness :
  ∀ {Δ : Con}{sΔ : Ctx Δ len}{σ : Stack Δ ms}{σ' : Stack Δ ns}{A' : Ty Δ n}{t' : Tm Δ A'}
    (ins : Is D sΔ σ (σ' ∷ t'))
    {env : Env D len}{st : Env D ms}{δ : Sub · Δ}
    (wf-env : env ⊨ sΔ as δ)(wf-st : wf-env ⊢ st ⊨ˢ σ) →
  b.Σ (Val D (t' [ δ ]))
      (λ v → I ⊢ conf ins env st (◆ (t' [ δ ])) wf-env wf-st b.refl b.refl ⇓ v)
TotalCorrectness {t' = t'} ins {δ = δ} wf-env wf-st
  with halts-frame (conf ins _ _ (◆ (t' [ δ ])) wf-env wf-st b.refl b.refl)
... | halts v (halt tr) hv = v b., Halt tr

-- Total correctness for complete programs (Corollary "Total correctness
-- for programs"): closed code with an empty initial stack.
TotalCorrectness-program :
  ∀ {σ : Stack · ns}{A : Ty · n}{t : Tm · A} (ins : Is D ◆ ◆ (σ ∷ t)) →
  b.Σ (Val D t) (λ v → I ⊢ conf ins ◆ ◆ (◆ t) nil nil b.refl b.refl ⇓ v)
TotalCorrectness-program ins = TotalCorrectness ins nil nil
