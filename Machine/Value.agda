module Machine.Value where

open import Agda.Primitive
import Lib.Basic as lib
open import Model.Shallow
open import Model.Context
open import Model.Labels
open import Model.Stack

open LCon

private variable
  i j k i' j' k' : Level
  Γ : Con i
  A : Ty Γ j
  B : Ty (Γ ▹ A) k
  l m n l' m' n' id : lib.ℕ
  sΓ : Ctx Γ l
  D : LCon

-- Representation of runtime values,
-- which knows what value in the syntax it implements.
-- (Treat pairs later)

mutual
  data Val (D : LCon) : {A : Ty · i} → Tm · A → Setω where
    --
    lit-b : (b : lib.Bool) → Val D (bool b)
    --
    lit-n : (n : lib.ℕ) → Val D (nat n)
    --
    ty : (A : Ty · i) → Val D A
    --
    clo : 
      (L : Pi D id sΓ A B)
      (σ : Env D n) → 
      ⦃ pf : sΓ ⊨ σ ⦄ → 
      Val D (_⟦_⟧ D L ⟦ pf ⟧⊨)

  -- Env, list of values, essentially runtime stacks
  data Env (D : LCon) : (n : lib.ℕ) → Setω where
    ◆ : Env D lib.zero
    _∷_ : {A : Ty · i}{t : Tm · A} → Env D n → Val D t → Env D (lib.suc n)

  -- Env that implements context
  data _⊨_ {D : LCon} : {Γ : Con i} → Ctx Γ n → Env D n → Setω where
    nil : ◆ ⊨ ◆
    --
    cons : 
        {A : Ty Γ j}{A' : Ty · j}
        {t : Tm Γ A}{t' : Tm · A'}{v : Val D t'}
        {sΓ : Ctx Γ n}{σ : Env D n} → 
      (pf : sΓ ⊨ σ) →  
      (eqA : A' lib.≡ A [ ⟦ pf ⟧⊨ ]T) → 
      (eqt : t' lib.≡ Tm-subst (t [ ⟦ pf ⟧⊨ ]) (lib.sym (lib.cong-app eqA))) → 
      ((sΓ ∷ A) ⊨ (σ ∷ v))

  ⟦_⟧⊨ : 
    {sΓ : Ctx Γ n} {σ : Env D n} (pf : sΓ ⊨ σ) → Sub · Γ
  ⟦_⟧⊨ nil = ε
  ⟦_⟧⊨ {σ = _∷_ {t = t} σ v} (cons pf eqA eqt) rewrite eqA = ⟦ pf ⟧⊨ ▻ t

-- Find the term at position x in an env that implements Γ
_[_]V : 
  {sΓ : Ctx Γ n}{σ : Env D n}
  (x : V sΓ A) (pf : sΓ ⊨ σ) → Tm · (A [ ⟦ pf ⟧⊨ ]T)
x [ pf ]V = ⟦ x ⟧V [ ⟦ pf ⟧⊨ ]

Val-subst : 
  {A A' : Ty · i}{t : Tm · A}
  (v : Val D t) (pf : A lib.≡ A') → Val D (Tm-subst t (lib.cong-app pf))
Val-subst v lib.refl = v

findᵉ : 
  {sΓ : Ctx Γ n}
  (env : Env D n)(x : V sΓ A) → 
  (pf : sΓ ⊨ env) → Val D (x [ pf ]V)
findᵉ (env ∷ v) vz (cons pf eqA eqt) rewrite eqA = v
findᵉ (env ∷ v) (vs x) (cons pf eqA eqt) rewrite eqA = findᵉ env x pf

takeᵉ : (n : lib.ℕ) → Env D (n lib.+ m) → Env D n
takeᵉ lib.zero env = ◆
takeᵉ (lib.suc n) (env ∷ v) = (takeᵉ n env) ∷ v

dropᵉ : (n : lib.ℕ) → Env D (n lib.+ m) → Env D m
dropᵉ lib.zero env = env
dropᵉ (lib.suc n) (env ∷ v) = dropᵉ n env

-- Judgement: a runtime stack implements a "virtural" stack
data _⊢_⊨ˢ_ {D : LCon} : {sΓ : Ctx Γ l} {env : Env D l} (wf : sΓ ⊨ env) → Stack Γ n → Env D n → Setω where
  nil : {env : Env D l}{wf : sΓ ⊨ env} → wf ⊢ ◆ {Γ = Γ} ⊨ˢ ◆
  --
  cons : 
    {env : Env D l}{wf : sΓ ⊨ env}
    {σ : Stack Γ n}{t : Tm Γ A}
    {st : Env D n}{v : Val D (t [ ⟦ wf ⟧⊨ ])} → 
    (pf : wf ⊢ σ ⊨ˢ st) → 
    wf ⊢ (σ ∷ t) ⊨ˢ (st ∷ v)  

findˢ : 
  {sΓ : Ctx Γ l}{env : Env D l}
  {wf : sΓ ⊨ env}{σ : Stack Γ n}
  (st : Env D n)(x : SVar σ A)
  (pf : wf ⊢ σ ⊨ˢ st) → Val D ((find σ x) [ ⟦ wf ⟧⊨ ])  
findˢ {σ = σ ∷ t} (st ∷ v) vz (cons pf) = v
findˢ (st ∷ t) (vs x) (cons pf) = findˢ st x pf

-- [subst] : σ ≡ δ → A [ σ ]T ≡ A [ δ ]T

tryy : {A B : Set}{f g : A → B}{x y : A} → x lib.≡ y → Set
tryy lib.refl = {!   !}

-- Given:
-- 1. env that implements Γ
-- 2. st that implements σ w.r.t. env
-- 3. Δ such that Γ ⊢ σ of Δ,
-- Have these mutual conclusions: (it has to be mutual, I think...)
mutual
  -- st implements Δ
  clo⊨ : 
    {env : Env D l}{Δ : Con i'}
    {sΔ : Ctx Δ n}{st : Env D n}{σ : Stack Γ n} → 
    (wf : sΓ ⊨ env) → wf ⊢ σ ⊨ˢ st → sΓ ⊢ σ of sΔ → sΔ ⊨ st 
  clo⊨ {sΔ = ◆} {◆} {◆} wf wf-st pf = nil
  clo⊨ {sΔ = sΔ ∷ A} {st ∷ v} {σ ∷ t} wf (cons wf-st) (cons ⦃ pf = pf ⦄) 
    = cons 
      (clo⊨ wf wf-st pf) 
      (lib.ext-⊤ (lib.cong A (lib.sym (⟦clo⟧⊨ wf wf-st pf)))) 
      {!   !}
    -- = cons (clo⊨ wf wf-st pf) 
    --   (lib.tran 
    --     ([∘]T {σ = ⟦ pf ⟧s} {δ = ⟦ wf ⟧⊨} {A = A}) 
    --     (lib.cong (λ x → A [ x ]T) (⟦clo⟧⊨ wf wf-st pf))
    --   )

--   -- When viewed as substitutions, s = σ ∘ env
  ⟦clo⟧⊨ : 
    {env : Env D l}{Δ : Con i}
    {sΔ : Ctx Δ n}{st : Env D n}{σ : Stack Γ n}
    (wf : sΓ ⊨ env)
    (wf-st : wf ⊢ σ ⊨ˢ st)
    (pf : sΓ ⊢ σ of sΔ) →
    ∀ {γ} → ⟦ clo⊨ wf wf-st pf ⟧⊨ γ lib.≡ ⟦ pf ⟧s (⟦ wf ⟧⊨ γ)
  ⟦clo⟧⊨ {sΔ = ◆} {◆} {◆} wf wf-st nil = lib.refl
  ⟦clo⟧⊨ {sΔ = sΔ ∷ A} {st ∷ v} {σ ∷ t} wf (cons wf-st) (cons ⦃ pf = pf ⦄)
    = {!  !}




 