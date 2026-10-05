module SECD.Theorem.Fundamental where

import Lib.Basic as b
open import Lib.Order

open import Model.Universe
open import Model.Shallow hiding (↓; ↓!)
open import Model.Context
open import Model.Stack

open import SECD.Syntax
open import SECD.Value
open import SECD.Config
open import SECD.Opsem

open import SECD.Theorem.Halting

-- Lemmas about the shallow model shared with the label-based machine
open Model.Shallow.Lemmas
open b using (ℕ; _≡_; _×_)

private variable
  m n len len* ms ms₀ ms* ns ns* nz lf : ℕ

{- Generic lemmas about halting at the current frame -}

-- A RET configuration halts with the value on top of its stack.
-- (The proofs relating the value to the abstract stack are arbitrary here:
-- this is where the conversion implicit in the definition of the halting
-- relation on stacks is discharged.)
RET-halts :
  ∀ {Γ Δ : Con}{sΔ : Ctx Δ len}{A : Ty Γ n}{s : Tm Γ A}{η : Sub · Γ}
    {σ : Stack Δ ms}{A' : Ty Δ n}{t' : Tm Δ A'}
    {env : Env len}{st : Env ms}{sf : Sf s η lf}{δ : Sub · Δ}
    {wf-env : env ⊨ sΔ as δ}{wf-st : wf-env ⊢ st ⊨ˢ σ}
    {tA : Type (b.suc n)}{t'' : Tm · (λ _ → tA)}{v : Val t''}
    (ptt : tA ≡ (A' [ δ ]T) b.tt) (eq : t' [ δ ] ≡ Tm-subst t'' ptt) → H v →
    (eq-A : A' [ δ ]T ≡ A [ η ]T)
    (eq-t : s [ η ] ≡ Tm-subst (t' [ δ ]) (b.cong-app eq-A)) →
  Halts (conf (RET {σ = σ ∷ t'}) env (st ∷ v) sf wf-env (cons wf-st ptt eq) eq-A eq-t)
RET-halts b.refl b.refl hv eq-A eq-t = halts _ (halt ■) hv

-- A step within the current frame preserves halting.
step-halts :
  ∀ {Γ Δ : Con}{sΔ : Ctx Δ len}{A : Ty Γ n}{s : Tm Γ A}{η : Sub · Γ}
    {σ₀ : Stack Δ ms₀}{σ₁ : Stack Δ ms}{σ' : Stack Δ ns}{A' : Ty Δ n}{t' : Tm Δ A'}
    {ins₀ : Is sΔ σ₀ (σ' ∷ t')}{ins₁ : Is sΔ σ₁ (σ' ∷ t')}
    {env : Env len}{st₀ : Env ms₀}{st₁ : Env ms}{sf : Sf s η lf}{δ : Sub · Δ}
    {wf-env : env ⊨ sΔ as δ}{wf-st₀ : wf-env ⊢ st₀ ⊨ˢ σ₀}{wf-st₁ : wf-env ⊢ st₁ ⊨ˢ σ₁}
    {eq-A : A' [ δ ]T ≡ A [ η ]T}
    {eq-t : s [ η ] ≡ Tm-subst (t' [ δ ]) (b.cong-app eq-A)} →
  conf ins₀ env st₀ sf wf-env wf-st₀ eq-A eq-t ↝ conf ins₁ env st₁ sf wf-env wf-st₁ eq-A eq-t →
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
    {ins : Is sΔ (σ ∷ t) (σ' ∷ t')}
    {env : Env len}{st : Env ms}{sf : Sf s η lf}{δ : Sub · Δ}
    {wf-env : env ⊨ sΔ as δ}{wf-st : wf-env ⊢ st ⊨ˢ σ}
    {eq-A : A' [ δ ]T ≡ A [ η ]T}
    {eq-t : s [ η ] ≡ Tm-subst (t' [ δ ]) (b.cong-app eq-A)}
    -- the caller, before the call
    {σ₀ : Stack Δ ms₀}{ins₀ : Is sΔ σ₀ (σ' ∷ t')}
    {st₀ : Env ms₀}{wf-st₀ : wf-env ⊢ st₀ ⊨ˢ σ₀}
    -- the callee
    {Δ* : Con}{sΔ* : Ctx Δ* len*}{σ* : Stack Δ* ms*}{σ*' : Stack Δ* ns*}
    {A* : Ty Δ* m}{t* : Tm Δ* A*}
    {ins* : Is sΔ* σ* (σ*' ∷ t*)}{env* : Env len*}{st* : Env ms*}{δ* : Sub · Δ*}
    {wf-env* : env* ⊨ sΔ* as δ*}{wf-st* : wf-env* ⊢ st* ⊨ˢ σ*}
    {eq-A* : A* [ δ* ]T ≡ B [ δ ]T}
    {eq-t* : t [ δ ] ≡ Tm-subst (t* [ δ* ]) (b.cong-app eq-A*)} →
  conf ins₀ env st₀ sf wf-env wf-st₀ eq-A eq-t
    ↝ conf ins* env* st* (sf ∷ fr ins env st wf-env wf-st eq-A eq-t) wf-env* wf-st* eq-A* eq-t* →
  Halts (conf ins* env* st* (sf ∷ fr ins env st wf-env wf-st eq-A eq-t) wf-env* wf-st* eq-A* eq-t*) →
  (∀ {tA : Type (b.suc m)}{t'' : Tm · (λ _ → tA)} (v : Val t'')
     (ptt : tA ≡ (B [ δ ]T) b.tt) (eq : t [ δ ] ≡ Tm-subst t'' ptt) → H v →
     Halts (conf ins env (st ∷ v) sf wf-env (cons wf-st ptt eq) eq-A eq-t)) →
  Halts (conf ins₀ env st₀ sf wf-env wf-st₀ eq-A eq-t)
call-halts step (halts v* (halt {eq-A = eqA} {eq-t = eqt} tr*) hv*) K
  with K v* (b.cong-app eqA) eqt hv*
... | halts v' (halt tr') hv' = halts v' (halt (step ⟫ (tr* ++* (C-RET ⟫ tr')))) hv'

{- The recursor -}

-- By induction on the natural number on top of the stack: if the zero
-- branch halts at the current frame, every closure of the successor
-- branch over a predecessor is in the halting relation, and the
-- continuation halts for every halting value of the result type, then the
-- recursor instruction followed by the continuation halts.
ITER-halts :
  ∀ (y : ℕ)
    {Γ Δ : Con}{sΔ : Ctx Δ len}{A : Ty Γ n}{s : Tm Γ A}{η : Sub · Γ}
    {σ : Stack Δ ms}{σ' : Stack Δ ns}{A' : Ty Δ n}{t' : Tm Δ A'}
    {x : Tm Δ Nat}
    {P : Ty (Δ ▹ Nat) m}
    {σz : Stack Δ nz}{z : Tm Δ (P [ ✧ ▻ zero ]T)}
    {Z : Is sΔ ◆ (σz ∷ z)}
    {σs : Stack (Δ ▹ Nat ▹ P) ns*}{s' : Tm (Δ ▹ Nat ▹ P) (P [ p² ▻ (suc 𝟙) ]T)}
    {S : Is (sΔ ∷ Nat ∷ P) ◆ (σs ∷ s')}
    (ins : Is sΔ (σ ∷ iter P z s' x) (σ' ∷ t'))
    {env : Env len}{st : Env ms}{sf : Sf s η lf}{δ : Sub · Δ}
    (wf-env : env ⊨ sΔ as δ) → Hᵉ wf-env →
    (wf-st : wf-env ⊢ st ⊨ˢ σ) →
    (eq-x : x [ δ ] ≡ nat y)
    (eq-A : A' [ δ ]T ≡ A [ η ]T)
    (eq-t : s [ η ] ≡ Tm-subst (t' [ δ ]) (b.cong-app eq-A)) →
    (∀ {Γ₀ : Con}{A₀ : Ty Γ₀ m}{s₀ : Tm Γ₀ A₀}{η₀ : Sub · Γ₀}{lf₀}
       (sf₀ : Sf s₀ η₀ lf₀)
       (eq-A₀ : (P [ ✧ ▻ zero ]T) [ δ ]T ≡ A₀ [ η₀ ]T)
       (eq-t₀ : s₀ [ η₀ ] ≡ Tm-subst (z [ δ ]) (b.cong-app eq-A₀)) →
       Halts (conf Z env ◆ sf₀ wf-env nil eq-A₀ eq-t₀)) →
    (∀ (y' : ℕ) → H (clo (env ∷ lit-n y') S ⦃ cons wf-env b.refl ⦄)) →
    (∀ {tA : Type (b.suc m)}{t'' : Tm · (λ _ → tA)} (v : Val t'')
       (ptt : tA ≡ ((P [ ✧ ▻ x ]T) [ δ ]T) b.tt)
       (eq : (iter P z s' x) [ δ ] ≡ Tm-subst t'' ptt) → H v →
       Halts (conf ins env (st ∷ v) sf wf-env (cons wf-st ptt eq) eq-A eq-t)) →
  Halts (conf (ITER P Z S >> ins) env (st ∷ lit-n y) sf wf-env (cons wf-st b.refl eq-x) eq-A eq-t)
ITER-halts b.zero ins wf-env hᵉ wf-st eq-x eq-A eq-t hZ hS K =
  call-halts C-ITER-Z (hZ _ _ _) K
ITER-halts {m = m} (b.suc y) {x = x} {P} {z = z} {Z} {s' = s'} {S} ins {env} {st} {sf} {δ}
  wf-env hᵉ wf-st eq-x eq-A eq-t hZ hS K =
  call-halts C-ITER-S
    (ITER-halts y (APP {f = lam s' [ ✧ ▻ nat y ]} >> RET)
      wf-env hᵉ (cons nil b.refl b.refl) b.refl _ _ hZ hS K')
    K
  where
    K' : ∀ {tA : Type (b.suc m)}{t'' : Tm · (λ _ → tA)} (v : Val t'')
           (ptt : tA ≡ ((P [ ✧ ▻ nat y ]T) [ δ ]T) b.tt)
           (eq : (iter P z s' (nat y)) [ δ ] ≡ Tm-subst t'' ptt) → H v →
         Halts (conf (APP {f = lam s' [ ✧ ▻ nat y ]} >> RET) env
                     (◆ ∷ clo (env ∷ lit-n y) S ⦃ cons wf-env b.refl ⦄ ∷ v)
                     (sf ∷ fr ins env st wf-env wf-st eq-A eq-t)
                     wf-env (cons (cons nil b.refl b.refl) ptt eq) _ _)
    K' v b.refl b.refl hv =
      call-halts C-APP
        (hS y v b.refl hv _ _ _)
        (λ v' ptt' eq' hv' → RET-halts ptt' eq' hv' _ _)

{- The fundamental lemma -}

mutual

  Fund :
    ∀ {Γ Δ : Con}{sΔ : Ctx Δ len}{A : Ty Γ n}{s : Tm Γ A}{η : Sub · Γ}
      {σ : Stack Δ ms}{σ' : Stack Δ ns}{A' : Ty Δ n}{t' : Tm Δ A'}
      (ins : Is sΔ σ (σ' ∷ t')) →
      {env : Env len}{st : Env ms}{sf : Sf s η lf}{δ : Sub · Δ}
      (wf-env : env ⊨ sΔ as δ) → Hᵉ wf-env →
      (wf-st : wf-env ⊢ st ⊨ˢ σ) → Hˢ wf-st →
      (eq-A : A' [ δ ]T ≡ A [ η ]T)
      (eq-t : s [ η ] ≡ Tm-subst (t' [ δ ]) (b.cong-app eq-A)) →
    Halts (conf ins env st sf wf-env wf-st eq-A eq-t)
  Fund RET wf-env hᵉ (cons wf-st ptt eq) (hˢ b., hv) eq-A eq-t =
    RET-halts ptt eq hv eq-A eq-t
  Fund (NOP >> ins) wf-env hᵉ wf-st hˢ eq-A eq-t =
    step-halts C-NOP (Fund ins wf-env hᵉ wf-st hˢ eq-A eq-t)
  Fund (VAR x >> ins) wf-env hᵉ wf-st hˢ eq-A eq-t =
    step-halts C-VAR
      (Fund ins wf-env hᵉ (cons wf-st b.refl b.refl) (hˢ b., Hᵉ-find wf-env hᵉ x) eq-A eq-t)
  Fund (POP >> ins) wf-env hᵉ (cons wf-st b.refl b.refl) (hˢ b., hv) eq-A eq-t =
    step-halts C-POP (Fund ins wf-env hᵉ wf-st hˢ eq-A eq-t)
  Fund (APP >> ins) wf-env hᵉ
    (cons {v = v} (cons {v = clo env' ins' ⦃ wf-env' ⦄} wf-st pA ptf) b.refl b.refl)
    ((hˢ b., hclo) b., hv) eq-A eq-t =
    call-halts C-APP
      (hclo v (b.sym (inj₁ pA)) (H-subst (b.sym (inj₁ pA)) hv) _ _ _)
      (λ v' ptt eq hv' → Fund ins wf-env hᵉ (cons wf-st ptt eq) (hˢ b., hv') eq-A eq-t)
  Fund (CLO ms' ins' ⦃ pf ⦄ >> ins) {env} {st} wf-env hᵉ wf-st hˢ eq-A eq-t =
    step-halts C-CLO
      (Fund ins wf-env hᵉ
        (cons {v = clo (takeᵉ ms' st) ins' ⦃ clo⊨ wf-env (⊨ˢ-take wf-st) pf ⦄}
              (⊨ˢ-drop wf-st) b.refl b.refl)
        (Hˢ-drop wf-st hˢ b.,
         H-clo ins' (clo⊨ wf-env (⊨ˢ-take wf-st) pf) (Hᵉ-clo⊨ wf-env (⊨ˢ-take wf-st) (Hˢ-take wf-st hˢ) pf))
        eq-A eq-t)
  Fund (PUSHC ins' >> ins) {env} wf-env hᵉ wf-st hˢ eq-A eq-t =
    step-halts C-PUSHC
      (Fund ins wf-env hᵉ (cons {v = clo env ins' ⦃ wf-env ⦄} wf-st b.refl b.refl)
        (hˢ b., H-clo ins' wf-env hᵉ) eq-A eq-t)
  Fund (LIT k >> ins) wf-env hᵉ wf-st hˢ eq-A eq-t =
    step-halts C-LIT (Fund ins wf-env hᵉ (cons wf-st b.refl b.refl) (hˢ b., tt₁) eq-A eq-t)
  Fund (TY B >> ins) wf-env hᵉ wf-st hˢ eq-A eq-t =
    step-halts C-TY (Fund ins wf-env hᵉ (cons wf-st b.refl b.refl) (hˢ b., tt₁) eq-A eq-t)
  Fund (SWP >> ins) wf-env hᵉ
    (cons (cons wf-st b.refl b.refl) b.refl b.refl) ((hˢ b., h₁) b., h₂) eq-A eq-t =
    step-halts C-SWP
      (Fund ins wf-env hᵉ (cons (cons wf-st b.refl b.refl) b.refl b.refl) ((hˢ b., h₂) b., h₁) eq-A eq-t)
  Fund (ST x >> ins) wf-env hᵉ wf-st hˢ eq-A eq-t =
    step-halts C-ST
      (Fund ins wf-env hᵉ (cons wf-st b.refl b.refl) (hˢ b., Hˢ-find wf-st hˢ x) eq-A eq-t)
  Fund (INC >> ins) wf-env hᵉ (cons {v = lit-n k} wf-st b.refl eq-x) (hˢ b., _) eq-A eq-t =
    step-halts C-INC
      (Fund ins wf-env hᵉ (cons wf-st b.refl (b.cong suc eq-x)) (hˢ b., tt₁) eq-A eq-t)
  Fund (ITER P Z S >> ins) wf-env hᵉ
    (cons {v = lit-n y} wf-st b.refl eq-x) (hˢ b., _) eq-A eq-t =
    ITER-halts y ins wf-env hᵉ wf-st eq-x eq-A eq-t
      (λ sf₀ eq-A₀ eq-t₀ → Fund Z wf-env hᵉ nil tt₁ eq-A₀ eq-t₀)
      (λ y' → H-clo S (cons wf-env b.refl) (hᵉ b., tt₁))
      (λ v ptt eq hv → Fund ins wf-env hᵉ (cons wf-st ptt eq) (hˢ b., hv) eq-A eq-t)
  Fund (UNIT >> ins) wf-env hᵉ wf-st hˢ eq-A eq-t =
    step-halts C-UNIT (Fund ins wf-env hᵉ (cons wf-st b.refl b.refl) (hˢ b., tt₁) eq-A eq-t)
  Fund (PAIR >> ins) wf-env hᵉ
    (cons (cons wf-st b.refl b.refl) b.refl b.refl) ((hˢ b., h₁) b., h₂) eq-A eq-t =
    step-halts C-PAIR
      (Fund ins wf-env hᵉ (cons wf-st b.refl b.refl) (hˢ b., (h₁ b., h₂)) eq-A eq-t)
  Fund (FST {p = t} >> ins) {δ = δ} wf-env hᵉ
    (cons {v = pair {B = B+} {t = t₁} {t' = t₂} v₁ v₂} wf-st pA ptf) (hˢ b., (h₁ b., h₂)) eq-A eq-t =
    step-halts C-FST
      (Fund ins wf-env hᵉ
        (cons {v = v₁} wf-st (Σ-inj₁ pA) (lemma-FST t δ (_,_ {B = B+} t₁ t₂) pA ptf))
        (hˢ b., h₁) eq-A eq-t)
  Fund (SND {p = t} >> ins) {δ = δ} wf-env hᵉ
    (cons {v = pair {B = B+} {t = t₁} {t' = t₂} v₁ v₂} wf-st pA ptf) (hˢ b., (h₁ b., h₂)) eq-A eq-t =
    step-halts C-SND
      (Fund ins wf-env hᵉ
        (cons {v = v₂} wf-st (Σ-inj₂ pA (lemma-SND1 t δ (_,_ {B = B+} t₁ t₂) pA ptf))
                              (lemma-SND2 t δ (_,_ {B = B+} t₁ t₂) pA ptf))
        (hˢ b., h₂) eq-A eq-t)
  Fund (UP >> ins) wf-env hᵉ (cons wf-st b.refl b.refl) (hˢ b., hv) eq-A eq-t =
    step-halts C-UP (Fund ins wf-env hᵉ (cons wf-st b.refl b.refl) (hˢ b., hv) eq-A eq-t)
  Fund (DOWN >> ins) wf-env hᵉ (cons {v = lift v} wf-st b.refl b.refl) (hˢ b., hv) eq-A eq-t =
    step-halts C-DOWN (Fund ins wf-env hᵉ (cons wf-st b.refl b.refl) (hˢ b., hv) eq-A eq-t)

  -- A closure over a halting environment is in the halting relation:
  -- the closure cases of the fundamental lemma, by the induction
  -- hypothesis on the code of the closure.
  H-clo :
    ∀ {Γ : Con}{sΓ : Ctx Γ len}{A : Ty Γ n}{B : Ty (Γ ▹ A) n}
      {σ' : Stack (Γ ▹ A) ns}{t : Tm (Γ ▹ A) B}
      (ins : Is (sΓ ∷ A) ◆ (σ' ∷ t))
      {env : Env len}{δ : Sub · Γ}
      (wf-env : env ⊨ sΓ as δ) → Hᵉ wf-env →
    H (clo env ins ⦃ wf-env ⦄)
  H-clo ins wf-env hᵉ v pA hv sf eq-A eq-t =
    Fund ins (cons wf-env pA) (hᵉ b., H-unsubst pA hv) nil tt₁ eq-A eq-t
