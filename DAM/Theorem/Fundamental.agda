open import DAM.Labels
open import DAM.Syntax

module DAM.Theorem.Fundamental {D : LCon} (I : Impl D) where

import Lib.Basic as b
open import Lib.Order

open import Model.Universe
open import Model.Shallow
open import Model.Context
open import Model.Stack

open import DAM.Value
open import DAM.Config
open import DAM.Opsem
open import DAM.Theorem.Halting
open Halting I

open b using (ℕ; _≡_; _×_)
open LCon

private variable
  m n len len* ms ms₀ ms* ns ns* lf id id' : ℕ

{- Generic lemmas about halting at the current frame -}

-- A RET configuration halts with the value on top of its stack.
-- (The proofs relating the value to the abstract stack are arbitrary here:
-- this is where the "conversion" implicit in the paper's Definition of H
-- on stacks is discharged.)
RET-halts :
  ∀ {Γ Δ : Con}{sΔ : Ctx Δ len}{A : Ty Γ n}{s : Tm Γ A}{η : Sub · Γ}
    {σ : Stack Δ ms}{A' : Ty Δ n}{t' : Tm Δ A'}
    {env : Env D len}{st : Env D ms}{sf : Sf D s η lf}{δ : Sub · Δ}
    {wf-env : env ⊨ sΔ as δ}{wf-st : wf-env ⊢ st ⊨ˢ σ}
    {tA : Type (b.suc n)}{t'' : Tm · (λ _ → tA)}{v : Val D t''}
    (ptt : tA ≡ (A' [ δ ]T) b.tt) (eq : t' [ δ ] ≡ Tm-subst t'' ptt) → H v →
    (eq-A : A' [ δ ]T ≡ A [ η ]T)
    (eq-t : s [ η ] ≡ Tm-subst (t' [ δ ]) (b.cong-app eq-A)) →
  Halts (conf (RET {σ = σ ∷ t'}) env (st ∷ v) sf wf-env (cons wf-st ptt eq) eq-A eq-t)
RET-halts b.refl b.refl hv eq-A eq-t = halts _ (halt ■) hv

-- A step within the current frame preserves halting.
step-halts :
  ∀ {Γ Δ : Con}{sΔ : Ctx Δ len}{A : Ty Γ n}{s : Tm Γ A}{η : Sub · Γ}
    {σ₀ : Stack Δ ms₀}{σ₁ : Stack Δ ms}{σ' : Stack Δ ns}{A' : Ty Δ n}{t' : Tm Δ A'}
    {ins₀ : Is D sΔ σ₀ (σ' ∷ t')}{ins₁ : Is D sΔ σ₁ (σ' ∷ t')}
    {env : Env D len}{st₀ : Env D ms₀}{st₁ : Env D ms}{sf : Sf D s η lf}{δ : Sub · Δ}
    {wf-env : env ⊨ sΔ as δ}{wf-st₀ : wf-env ⊢ st₀ ⊨ˢ σ₀}{wf-st₁ : wf-env ⊢ st₁ ⊨ˢ σ₁}
    {eq-A : A' [ δ ]T ≡ A [ η ]T}
    {eq-t : s [ η ] ≡ Tm-subst (t' [ δ ]) (b.cong-app eq-A)} →
  I ⊢ conf ins₀ env st₀ sf wf-env wf-st₀ eq-A eq-t ↝ conf ins₁ env st₁ sf wf-env wf-st₁ eq-A eq-t →
  Halts (conf ins₁ env st₁ sf wf-env wf-st₁ eq-A eq-t) →
  Halts (conf ins₀ env st₀ sf wf-env wf-st₀ eq-A eq-t)
step-halts s (halts v (halt tr) hv) = halts v (halt (s ⟫ tr)) hv

-- Calling and returning: if the caller steps into a callee configuration
-- (whose top call frame is the caller's), the callee halts at its own
-- frame, and the caller's continuation halts for every halting value it
-- may receive, then the caller halts.
call-halts :
  ∀ {Γ Δ : Con}{sΔ : Ctx Δ len}{A : Ty Γ n}{s : Tm Γ A}{η : Sub · Γ}
    {σ : Stack Δ ms}{σ' : Stack Δ ns}{A' : Ty Δ n}{t' : Tm Δ A'}
    {B : Ty Δ m}{t : Tm Δ B}
    {ins : Is D sΔ (σ ∷ t) (σ' ∷ t')}
    {env : Env D len}{st : Env D ms}{sf : Sf D s η lf}{δ : Sub · Δ}
    {wf-env : env ⊨ sΔ as δ}{wf-st : wf-env ⊢ st ⊨ˢ σ}
    {eq-A : A' [ δ ]T ≡ A [ η ]T}
    {eq-t : s [ η ] ≡ Tm-subst (t' [ δ ]) (b.cong-app eq-A)}
    -- the caller, before the call
    {σ₀ : Stack Δ ms₀}{ins₀ : Is D sΔ σ₀ (σ' ∷ t')}
    {st₀ : Env D ms₀}{wf-st₀ : wf-env ⊢ st₀ ⊨ˢ σ₀}
    -- the callee
    {Δ* : Con}{sΔ* : Ctx Δ* len*}{σ* : Stack Δ* ms*}{σ*' : Stack Δ* ns*}
    {A* : Ty Δ* m}{t* : Tm Δ* A*}
    {ins* : Is D sΔ* σ* (σ*' ∷ t*)}{env* : Env D len*}{st* : Env D ms*}{δ* : Sub · Δ*}
    {wf-env* : env* ⊨ sΔ* as δ*}{wf-st* : wf-env* ⊢ st* ⊨ˢ σ*}
    {eq-A* : A* [ δ* ]T ≡ B [ δ ]T}
    {eq-t* : t [ δ ] ≡ Tm-subst (t* [ δ* ]) (b.cong-app eq-A*)} →
  I ⊢ conf ins₀ env st₀ sf wf-env wf-st₀ eq-A eq-t
    ↝ conf ins* env* st* (sf ∷ fr ins env st wf-env wf-st eq-A eq-t) wf-env* wf-st* eq-A* eq-t* →
  Halts (conf ins* env* st* (sf ∷ fr ins env st wf-env wf-st eq-A eq-t) wf-env* wf-st* eq-A* eq-t*) →
  (∀ {tA : Type (b.suc m)}{t'' : Tm · (λ _ → tA)} (v : Val D t'')
     (ptt : tA ≡ (B [ δ ]T) b.tt) (eq : t [ δ ] ≡ Tm-subst t'' ptt) → H v →
     Halts (conf ins env (st ∷ v) sf wf-env (cons wf-st ptt eq) eq-A eq-t)) →
  Halts (conf ins₀ env st₀ sf wf-env wf-st₀ eq-A eq-t)
call-halts step (halts v* (halt {eq-A = eqA} {eq-t = eqt} tr*) hv*) K
  with K v* (b.cong-app eqA) eqt hv*
... | halts v' (halt tr') hv' = halts v' (halt (step ⟫ (tr* ++* (C-RET ⟫ tr')))) hv'

{- The recursor -}

-- The "Proposition" inside the rec case of the paper's fundamental lemma,
-- by induction on the natural number on top of the stack:
-- if the continuation halts for every halting value of the result type,
-- then the recursor instruction followed by the continuation halts.
ITER-halts :
  ∀ (y : ℕ)
    {Γ Δ : Con}{sΔ : Ctx Δ len}{A : Ty Γ n}{s : Tm Γ A}{η : Sub · Γ}
    {σ : Stack Δ ms}{σ' : Stack Δ ns}{A' : Ty Δ n}{t' : Tm Δ A'}
    {x : Tm Δ Nat}
    {P : Ty (Δ ▹ Nat) m}
    {Z : Pi D id sΔ (⊤n m) (P [ p ▻ zero ]T)}
    {S : Pi D id' (sΔ ∷ Nat) P (P [ p² ▻ (suc 𝟙) ]T)}
    (ins : Is D sΔ (σ ∷ iter P ((interp D Z) [ ✧ ▻ ttn ]) (interp D S) x) (σ' ∷ t'))
    {env : Env D len}{st : Env D ms}{sf : Sf D s η lf}{δ : Sub · Δ}
    (wf-env : env ⊨ sΔ as δ) → Hᵉ wf-env →
    (wf-st : wf-env ⊢ st ⊨ˢ σ) →
    (eq-x : x [ δ ] ≡ nat y)
    (eq-A : A' [ δ ]T ≡ A [ η ]T)
    (eq-t : s [ η ] ≡ Tm-subst (t' [ δ ]) (b.cong-app eq-A)) →
    H-Pi Z → H-Pi S →
    (∀ {tA : Type (b.suc m)}{t'' : Tm · (λ _ → tA)} (v : Val D t'')
       (ptt : tA ≡ ((P [ ✧ ▻ x ]T) [ δ ]T) b.tt)
       (eq : (iter P ((interp D Z) [ ✧ ▻ ttn ]) (interp D S) x) [ δ ] ≡ Tm-subst t'' ptt) → H v →
       Halts (conf ins env (st ∷ v) sf wf-env (cons wf-st ptt eq) eq-A eq-t)) →
  Halts (conf (ITER P Z S >> ins) env (st ∷ lit-n y) sf wf-env (cons wf-st b.refl eq-x) eq-A eq-t)
ITER-halts b.zero ins wf-env hᵉ wf-st eq-x eq-A eq-t h-labZ h-labS K =
  call-halts C-ITER-Z (h-labZ wf-env hᵉ lit-⊤ b.refl b.tt _ _ _) K
ITER-halts {m = m} (b.suc y) {x = x} {P} {Z} {S} ins {env} {st} {sf} {δ} wf-env hᵉ wf-st eq-x eq-A eq-t h-labZ h-labS K =
  call-halts C-ITER-S
    (ITER-halts y (APP {f = lapp D S (✧ ▻ nat y)} >> RET)
      wf-env hᵉ (cons nil b.refl b.refl) b.refl _ _ h-labZ h-labS K')
    K
  where
    K' : ∀ {tA : Type (b.suc m)}{t'' : Tm · (λ _ → tA)} (v : Val D t'')
           (ptt : tA ≡ ((P [ ✧ ▻ nat y ]T) [ δ ]T) b.tt)
           (eq : (iter P ((interp D Z) [ ✧ ▻ ttn ]) (interp D S) (nat y)) [ δ ] ≡ Tm-subst t'' ptt) → H v →
         Halts (conf (APP {f = lapp D S (✧ ▻ nat y)} >> RET) env
                     (◆ ∷ clo S (env ∷ lit-n y) ⦃ cons wf-env b.refl ⦄ ∷ v)
                     (sf ∷ fr ins env st wf-env wf-st eq-A eq-t)
                     wf-env (cons (cons nil b.refl b.refl) ptt eq) _ _)
    K' v b.refl b.refl hv =
      call-halts C-APP
        (h-labS (cons wf-env b.refl) (hᵉ b., b.tt) v b.refl hv _ _ _)
        (λ v' ptt' eq' hv' → RET-halts ptt' eq' hv' _ _)

{- The fundamental lemma -}

Fund :
  ∀ {Γ Δ : Con}{sΔ : Ctx Δ len}{A : Ty Γ n}{s : Tm Γ A}{η : Sub · Γ}
    {σ : Stack Δ ms}{σ' : Stack Δ ns}{A' : Ty Δ n}{t' : Tm Δ A'}
    (ins : Is D sΔ σ (σ' ∷ t')) → H-Is ins →
    {env : Env D len}{st : Env D ms}{sf : Sf D s η lf}{δ : Sub · Δ}
    (wf-env : env ⊨ sΔ as δ) → Hᵉ wf-env →
    (wf-st : wf-env ⊢ st ⊨ˢ σ) → Hˢ wf-st →
    (eq-A : A' [ δ ]T ≡ A [ η ]T)
    (eq-t : s [ η ] ≡ Tm-subst (t' [ δ ]) (b.cong-app eq-A)) →
  Halts (conf ins env st sf wf-env wf-st eq-A eq-t)
Fund RET hⁱ wf-env hᵉ (cons wf-st ptt eq) (hˢ b., hv) eq-A eq-t =
  RET-halts ptt eq hv eq-A eq-t
Fund (NOP >> ins) hⁱ wf-env hᵉ wf-st hˢ eq-A eq-t =
  step-halts C-NOP (Fund ins hⁱ wf-env hᵉ wf-st hˢ eq-A eq-t)
Fund (VAR x >> ins) hⁱ wf-env hᵉ wf-st hˢ eq-A eq-t =
  step-halts C-VAR
    (Fund ins hⁱ wf-env hᵉ (cons wf-st b.refl b.refl) (hˢ b., Hᵉ-find wf-env hᵉ x) eq-A eq-t)
Fund (POP >> ins) hⁱ wf-env hᵉ (cons wf-st b.refl b.refl) (hˢ b., hv) eq-A eq-t =
  step-halts C-POP (Fund ins hⁱ wf-env hᵉ wf-st hˢ eq-A eq-t)
Fund (APP >> ins) hⁱ wf-env hᵉ
  (cons {v = v} (cons {v = clo L env' ⦃ wf-env' ⦄} wf-st pA ptf) b.refl b.refl)
  ((hˢ b., hclo) b., hv) eq-A eq-t =
  call-halts C-APP
    (hclo v (b.sym (inj₁ pA)) (H-subst (b.sym (inj₁ pA)) hv) _ _ _)
    (λ v' ptt eq hv' → Fund ins hⁱ wf-env hᵉ (cons wf-st ptt eq) (hˢ b., hv') eq-A eq-t)
Fund (CLO ms' L ⦃ pf ⦄ >> ins) (h-lab b., hⁱ) {env} {st} wf-env hᵉ wf-st hˢ eq-A eq-t =
  step-halts C-CLO
    (Fund ins hⁱ wf-env hᵉ
      (cons {v = clo L (takeᵉ ms' st) ⦃ clo⊨ wf-env (⊨ˢ-take wf-st) pf ⦄}
            (⊨ˢ-drop wf-st) b.refl b.refl)
      (Hˢ-drop wf-st hˢ b.,
       h-lab (clo⊨ wf-env (⊨ˢ-take wf-st) pf) (Hᵉ-clo⊨ wf-env (⊨ˢ-take wf-st) (Hˢ-take wf-st hˢ) pf))
      eq-A eq-t)
Fund (CLOENV L >> ins) (h-lab b., hⁱ) {env} wf-env hᵉ wf-st hˢ eq-A eq-t =
  step-halts C-CLOENV
    (Fund ins hⁱ wf-env hᵉ (cons {v = clo L env ⦃ wf-env ⦄} wf-st b.refl b.refl)
      (hˢ b., h-lab wf-env hᵉ) eq-A eq-t)
Fund (LIT k >> ins) hⁱ wf-env hᵉ wf-st hˢ eq-A eq-t =
  step-halts C-LIT (Fund ins hⁱ wf-env hᵉ (cons wf-st b.refl b.refl) (hˢ b., b.tt) eq-A eq-t)
Fund (TY B >> ins) hⁱ wf-env hᵉ wf-st hˢ eq-A eq-t =
  step-halts C-TY (Fund ins hⁱ wf-env hᵉ (cons wf-st b.refl b.refl) (hˢ b., b.tt) eq-A eq-t)
Fund (SWP >> ins) hⁱ wf-env hᵉ
  (cons (cons wf-st b.refl b.refl) b.refl b.refl) ((hˢ b., h₁) b., h₂) eq-A eq-t =
  step-halts C-SWP
    (Fund ins hⁱ wf-env hᵉ (cons (cons wf-st b.refl b.refl) b.refl b.refl) ((hˢ b., h₂) b., h₁) eq-A eq-t)
Fund (ST x >> ins) hⁱ wf-env hᵉ wf-st hˢ eq-A eq-t =
  step-halts C-ST
    (Fund ins hⁱ wf-env hᵉ (cons wf-st b.refl b.refl) (hˢ b., Hˢ-find wf-st hˢ x) eq-A eq-t)
Fund (INC >> ins) hⁱ wf-env hᵉ (cons {v = lit-n k} wf-st b.refl eq-x) (hˢ b., _) eq-A eq-t =
  step-halts C-INC
    (Fund ins hⁱ wf-env hᵉ (cons wf-st b.refl (b.cong suc eq-x)) (hˢ b., b.tt) eq-A eq-t)
Fund (ITER P Z S >> ins) ((h-labZ b., h-labS) b., hⁱ) wf-env hᵉ
  (cons {v = lit-n y} wf-st b.refl eq-x) (hˢ b., _) eq-A eq-t =
  ITER-halts y ins wf-env hᵉ wf-st eq-x eq-A eq-t h-labZ h-labS
    (λ v ptt eq hv → Fund ins hⁱ wf-env hᵉ (cons wf-st ptt eq) (hˢ b., hv) eq-A eq-t)
Fund (UNIT >> ins) hⁱ wf-env hᵉ wf-st hˢ eq-A eq-t =
  step-halts C-UNIT (Fund ins hⁱ wf-env hᵉ (cons wf-st b.refl b.refl) (hˢ b., b.tt) eq-A eq-t)
Fund (PAIR >> ins) hⁱ wf-env hᵉ
  (cons (cons wf-st b.refl b.refl) b.refl b.refl) ((hˢ b., h₁) b., h₂) eq-A eq-t =
  step-halts C-PAIR
    (Fund ins hⁱ wf-env hᵉ (cons wf-st b.refl b.refl) (hˢ b., (h₁ b., h₂)) eq-A eq-t)
Fund (FST {p = t} >> ins) hⁱ {δ = δ} wf-env hᵉ
  (cons {v = pair {B = B+} {t = t₁} {t' = t₂} v₁ v₂} wf-st pA ptf) (hˢ b., (h₁ b., h₂)) eq-A eq-t =
  step-halts C-FST
    (Fund ins hⁱ wf-env hᵉ
      (cons {v = v₁} wf-st (Σ-inj₁ pA) (lemma-FST t δ (_,_ {B = B+} t₁ t₂) pA ptf))
      (hˢ b., h₁) eq-A eq-t)
Fund (SND {p = t} >> ins) hⁱ {δ = δ} wf-env hᵉ
  (cons {v = pair {B = B+} {t = t₁} {t' = t₂} v₁ v₂} wf-st pA ptf) (hˢ b., (h₁ b., h₂)) eq-A eq-t =
  step-halts C-SND
    (Fund ins hⁱ wf-env hᵉ
      (cons {v = v₂} wf-st (Σ-inj₂ pA (lemma-SND1 t δ (_,_ {B = B+} t₁ t₂) pA ptf))
                            (lemma-SND2 t δ (_,_ {B = B+} t₁ t₂) pA ptf))
      (hˢ b., h₂) eq-A eq-t)
Fund (UP >> ins) hⁱ wf-env hᵉ (cons wf-st b.refl b.refl) (hˢ b., hv) eq-A eq-t =
  step-halts C-UP (Fund ins hⁱ wf-env hᵉ (cons wf-st b.refl b.refl) (hˢ b., hv) eq-A eq-t)
Fund (DOWN >> ins) hⁱ wf-env hᵉ (cons {v = lift v} wf-st b.refl b.refl) (hˢ b., hv) eq-A eq-t =
  step-halts C-DOWN (Fund ins hⁱ wf-env hᵉ (cons wf-st b.refl b.refl) (hˢ b., hv) eq-A eq-t)
