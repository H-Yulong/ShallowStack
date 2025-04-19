module Machine.Value where

open import Agda.Primitive

import Lib.Basic as b
open import Lib.Order

open import Model.Universe
open import Model.Shallow
open import Model.Context
open import Model.Labels
open import Model.Stack

open LCon

private variable
  id n ms ns nv len : b.ℕ
  Γ : Con
  sΓ : Ctx Γ len
  D : LCon

-- Representation of runtime values,
-- which knows what value in the syntax it implements.
-- (Treat pairs later)

-- record ClosedType : Set where
--   -- constructor 
--   field
--     {lv} : b.ℕ
--     {A} : Type (b.suc lv)
--     t : Tm · (λ _ → A)

mutual
  data Val (D : LCon) : {A : Type (b.suc n)} → Tm · (λ _ → A) → Set₁ where
    --
    lit-b : (b : b.Bool) → Val D (bool b)
    --
    lit-n : (n : b.ℕ) → Val D (nat n)
    --
    ty : (A : Ty · n) → Val D (c A)
    --
    clo : 
      ∀ {A : Ty Γ n}{B : Ty (Γ ▹ A) n}{δ : Sub · Γ}
        -- {tA : Type (b.suc n)}
        -- -- -- {tB : ⟦ tA ⟧ → Type (b.suc n)}
        -- {ptt : ((Π A B) [ δ ]T) b.tt b.≡ `Π tA tB}
        (L : Pi D id sΓ A B)
        (σ : Env D nv) → 
        ⦃ pf : σ ⊨ sΓ as δ ⦄ → 
      -------------------------
      Val D (lapp D L δ)

  -- Env, list of values, essentially runtime stacks
  data Env (D : LCon) : (nv : b.ℕ) → Set₁ where
    ◆ : Env D b.zero
    _∷_ : {A : Type (b.suc n)}{t : Tm · (λ _ → A)} → Env D nv → Val D t → Env D (b.suc nv)

  -- Env that implements context
  data _⊨_as_ {D : LCon} : Env D nv → Ctx Γ len → Sub · Γ → Set₁ where
    nil : ◆ ⊨ ◆ as ε
    --
    cons : 
      {A : Ty Γ n}{sΓ : Ctx Γ len}
      {σ : Env D nv}{δ : Sub · Γ}
      {t : Tm · (A [ δ ]T)}{v : Val D t}
      (pf : σ ⊨ sΓ as δ) →
      ((σ ∷ v) ⊨ (sΓ ∷ A) as (δ ▻ t))


-- Find the term at position x in an env that implements Γ
_[_]V : 
  {A : Ty Γ n}{sΓ : Ctx Γ len}{σ : Env D len}{δ : Sub · Γ}
  (x : V sΓ A) (pf : σ ⊨ sΓ as δ) → Tm · (A [ δ ]T)
_[_]V {δ = δ} x pf = ⟦ x ⟧V [ δ ]

-- Val-subst : 
--   {A A' : Ty · n}{t : Tm · A}
--   (v : Val D t) (pf : A b.≡ A') → Val D (Tm-subst t (b.cong-app pf))
-- Val-subst v b.refl = v

findᵉ : 
  {A : Ty Γ n}{sΓ : Ctx Γ len}{δ : Sub · Γ}
  (env : Env D len)(x : V sΓ A) → 
  (pf : env ⊨ sΓ as δ) → Val D (x [ pf ]V)
findᵉ {δ = δ} (env ∷ v) vz (cons pf) = v
findᵉ (env ∷ v) (vs x) (cons pf) = findᵉ env x pf

takeᵉ : (ns : b.ℕ) → Env D (ns b.+ ms) → Env D ns
takeᵉ b.zero env = ◆
takeᵉ (b.suc n) (env ∷ v) = (takeᵉ n env) ∷ v

dropᵉ : (ns : b.ℕ) → Env D (ns b.+ ms) → Env D ms
dropᵉ b.zero env = env
dropᵉ (b.suc n) (env ∷ v) = dropᵉ n env

-- Judgement: a runtime stack implements a "virtural" stack
data _⊢_⊨ˢ_ {D : LCon} {sΓ : Ctx Γ len} {env : Env D len} {δ : Sub · Γ} 
  (wf : env ⊨ sΓ as δ) : Env D n → Stack Γ n → Set₁ where
----
  nil : wf ⊢ ◆ ⊨ˢ ◆
  --
  cons : 
    ∀ {A : Ty Γ n}{t : Tm Γ A}
      {tA : Type (b.suc n)}
      {σ : Stack Γ ns}{t' : Tm · (λ _ → tA)}
      {st : Env D ns}
      {v : Val D t'} → 
      (pf : wf ⊢ st ⊨ˢ σ) →
      (ptt : tA b.≡ (A [ δ ]T) b.tt) →  
      (eq : t [ δ ] b.≡ Tm-subst t' ptt) → 
    wf ⊢ (st ∷ v) ⊨ˢ (σ ∷ t)  
  -- I have to take the explicit equality here because function label's congruence
  -- under substitution is not refl, since label contexts are given as a signature.
  -- It doesn't hurt the development so far...

Lemma1 : 
  ∀ {D : LCon}{tA : Type (b.suc n)}
    {tB : ⟦ tA ⟧ → Type (b.suc n)}
    {f : Tm · (λ _ → `Π tA tB)} → 
    Val D f → 
    Set
Lemma1 (clo L σ) = b.ℕ

Lemma2 :
    ∀ {D : LCon} 
      -- env setup
      {Γ : Con}{sΓ : Ctx Γ len}
      {env : Env D len}{δ : Sub · Γ}
      {wf : env ⊨ sΓ as δ}
      -- abstract types and terms
      {A : Ty Γ n}{B : Ty (Γ ▹ A) n}
      {f : Tm Γ (Π A B)}
      -- codes and values
      -- {T : Type (b.suc n)}
      -- {t' : Tm · (λ _ → T)}
      -- {v : Val D T t'}
      -- stacks 
      {σ : Stack Γ ns}
      {st : Env D (b.suc ns)} → 
      --
    wf ⊢ st ⊨ˢ (σ ∷ f) →
    b.Σ b.ℕ (λ nv → Env D nv)
Lemma2 {σ = σ} {st = st ∷ clo {nv = nv} L σ'} (cons arg k eq) = nv b., σ'
-- Lemma2 {T = `Π tA tB} {v = clo L σ} (cons arg ptt eq) = {!   !}

{-
v : Val D (`Π (A (δ (record {}))) (λ a → B (δ (record {}) ~, a))) t'

      ∀ {A : Ty Γ n}{B : Ty (Γ ▹ A) n}{δ : Sub · Γ}
        (L : Pi D id sΓ A B)
        (σ : Env D nv) → 
        ⦃ pf : σ ⊨ sΓ as δ ⦄ → 
      Val D (`Π ((A [ δ ]T) b.tt) (λ a → (B [ δ ^ A ]T) (b.tt ~, a))) (lapp D L δ)

-}


{-
findˢ : 
  {sΓ : Ctx Γ l}{env : Env D l}{δ : Sub · Γ}
  {wf : sΓ ⊨ env as δ}{σ : Stack Γ n}
  (st : Env D n)(x : SVar σ A)
  (pf : wf ⊢ σ ⊨ˢ st) → Val D ((find σ x) [ δ ])  
findˢ {σ = σ ∷ t} (st ∷ v) vz (cons pf eq) rewrite eq = v
findˢ (st ∷ t) (vs x) (cons pf _) = findˢ st x pf

-- Given:
-- 1. env that implements Γ as δ
-- 2. st that implements σ w.r.t. env
-- 3. Δ such that Γ ⊢ σ of Δ as η
-- Have st implementing Δ as (η ∘ δ)
clo⊨ : 
  {env : Env D l}{Δ : Con i'}{δ : Sub · Γ}{η : Sub Γ Δ}
  {sΔ : Ctx Δ n}{st : Env D n}{σ : Stack Γ n} → 
  (wf : sΓ ⊨ env as δ) → wf ⊢ σ ⊨ˢ st → sΓ ⊢ σ of sΔ as η → sΔ ⊨ st as (η ∘ δ)
clo⊨ {sΔ = ◆} {◆} {◆} wf wf-st pf = nil
clo⊨ {sΔ = sΔ ∷ A} {st ∷ v} {σ ∷ t} wf (cons wf-st eq) (cons ⦃ pf ⦄) rewrite eq
  = cons (clo⊨ wf wf-st pf)

⊨ˢ-take : 
  {sΓ : Ctx Γ l}{env : Env D l}{δ : Sub · Γ}
  {wf : sΓ ⊨ env as δ}{σ : Stack Γ (n b.+ m)}{st : Env D (n b.+ m)} → 
  wf ⊢ σ ⊨ˢ st → wf ⊢ (take n σ) ⊨ˢ (takeᵉ n st)
⊨ˢ-take {n = b.zero} pf = nil
⊨ˢ-take {n = b.suc n} (cons pf eq) rewrite eq = cons (⊨ˢ-take pf) b.refl
-}

  
   