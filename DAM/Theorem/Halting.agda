module DAM.Theorem.Halting where

open import Agda.Primitive using (lzero; lsuc)
import Lib.Basic as b
open import Lib.Order

open import Model.Universe
open import Model.Shallow
open import Model.Context
open import Model.Stack

open import DAM.Labels
open import DAM.Syntax
open import DAM.Value
open import DAM.Config
open import DAM.Opsem

open b using (ℕ; _≡_; _×_)
open LCon

private variable
  m n len ms ns lf id : ℕ

-- Concatenation of reduction sequences
infixr 20 _++*_
_++*_ : ∀{D : LCon}{I : Impl D}{c c' c'' : Config D} →
  I ⊢ c ↝* c' → I ⊢ c' ↝* c'' → I ⊢ c ↝* c''
■ ++* tr = tr
(s ⟫ tr) ++* tr' = s ⟫ (tr ++* tr')

-- Transporting a value along an equation between closed types
Val-subst :
  ∀ {D : LCon}{tA A : Type (b.suc n)}{a : Tm · (λ _ → tA)} →
  (pA : tA ≡ A) → Val D a → Val D (Tm-subst a pA)
Val-subst b.refl v = v

{- Halting at the current frame -}

-- [I ⊢ c ↓ v] : the configuration c reduces to a RET configuration whose
-- stack of call frames is that of c, whose abstract return value and
-- closing substitution are those of c, and whose top stack value is v.
-- (Within a frame, the code, environment, closing substitution and the
-- final abstract value never change, so this is the only sensible notion
-- of "halting at the current frame".)
data _⊢_↓_ {D : LCon} (I : Impl D) (c : Config D) :
  Val D (Config.t' c [ Config.δ c ]) → Set₁ where
  halt :
    ∀ {σ : Stack (Config.Δ c) ns}
      {env : Env D (Config.len c)}
      {st : Env D ns}
      {v : Val D (Config.t' c [ Config.δ c ])}
      {wf-env : env ⊨ Config.sΔ c as Config.δ c}
      {wf-st : wf-env ⊢ st ⊨ˢ σ}
      {eq-A : Config.A' c [ Config.δ c ]T ≡ Config.A c [ Config.η c ]T}
      {eq-t : Config.s c [ Config.η c ] ≡ Tm-subst (Config.t' c [ Config.δ c ]) (b.cong-app eq-A)} →
    I ⊢ c ↝* conf (RET {σ = σ ∷ Config.t' c}) env (st ∷ v) (Config.sf c)
                  wf-env (cons wf-st b.refl b.refl) eq-A eq-t →
    ----------------------------------------------------------------
    I ⊢ c ↓ v

module Halting {D : LCon} (I : Impl D) where

  -- c halts at the current frame with a value satisfying P
  record HaltsWith (c : Config D) (P : Val D (Config.t' c [ Config.δ c ]) → Set₁) : Set₁ where
    constructor halts
    field
      val : Val D (Config.t' c [ Config.δ c ])
      trace : I ⊢ c ↓ val
      good : P val

  {- The halting relation on values -}

  -- Π-case: v is a closure, and running its code on any halting argument
  -- halts at the current frame (for every frame stack) with a halting result.
  HΠ :
    ∀ {A : Type (b.suc n)}{B : ⟦ uni (Type n) ⟦_⟧ ~~ A ⟧ → Type (b.suc n)}
      (HA : ∀ {a : Tm · (λ _ → A)} → Val D a → Set₁)
      (HB : ∀ (x : ⟦ uni (Type n) ⟦_⟧ ~~ A ⟧){b : Tm · (λ _ → B x)} → Val D b → Set₁)
      {f : Tm · (λ _ → `Π A B)} →
    Val D f → Set₁
  HΠ HA HB (clo {A = A₁} {B = B₁} {δ = δ'} L env' ⦃ wf-env' ⦄) =
    ∀ {tA : Type (b.suc _)}{a : Tm · (λ _ → tA)}
      (v : Val D a) (pA : tA ≡ (A₁ [ δ' ]T) b.tt) → HA (Val-subst pA v) →
    ∀ {Γ : Con}{A₀ : Ty Γ _}{s : Tm Γ A₀}{η : Sub · Γ}{lf}
      (sf : Sf D s η lf)
      (eq-A : B₁ [ δ' ▻ Tm-subst a pA ]T ≡ A₀ [ η ]T)
      (eq-t : s [ η ] ≡ Tm-subst (interp D L [ δ' ▻ Tm-subst a pA ]) (b.cong-app eq-A)) →
    HaltsWith (conf (Proc.instr (I L)) (env' ∷ v) ◆ sf (cons wf-env' pA) nil eq-A eq-t)
              (HB (Tm-subst a pA ~$ b.tt))

  -- Σ-case: both components halt.
  HΣ :
    ∀ {A : Type (b.suc n)}{B : ⟦ uni (Type n) ⟦_⟧ ~~ A ⟧ → Type (b.suc n)}
      (HA : ∀ {a : Tm · (λ _ → A)} → Val D a → Set₁)
      (HB : ∀ (x : ⟦ uni (Type n) ⟦_⟧ ~~ A ⟧){b : Tm · (λ _ → B x)} → Val D b → Set₁)
      {p : Tm · (λ _ → `Σ A B)} →
    Val D p → Set₁
  HΣ HA HB (pair {t = t₁} v₁ v₂) = HA v₁ × HB (t₁ ~$ b.tt) v₂

  -- Lifting case: the underlying value halts.
  H↑ :
    ∀ {A : Type (b.suc n)}
      (HA : ∀ {a : Tm · (λ _ → A)} → Val D a → Set₁)
      {t : Tm · (λ _ → `↑ A)} →
    Val D t → Set₁
  H↑ HA (lift v) = HA v

  -- The halting relation, by recursion on the code of the closed type.
  -- Base types, universes and identity types: every well-typed value halts.
  H : ∀ {n} {A : Type (b.suc n)} {t : Tm · (λ _ → A)} → Val D t → Set₁
  H {A = `N} v = b.⊤
  H {A = `B} v = b.⊤
  H {A = `⊤} v = b.⊤
  H {A = `⊥} v = b.⊤
  H {A = `U} v = b.⊤
  H {A = `Id A x y} v = b.⊤
  H {A = `Π A B} v = HΠ (H {A = A}) (λ x → H {A = B x}) v
  H {A = `Σ A B} v = HΣ (H {A = A}) (λ x → H {A = B x}) v
  H {n = b.zero} {A = `↑ ()} v
  H {n = b.suc n} {A = `↑ A} v = H↑ (H {A = A}) v

  -- Halting is invariant under transport along type equations
  H-subst :
    ∀ {tA A : Type (b.suc n)}{a : Tm · (λ _ → tA)}{v : Val D a} →
    (pA : tA ≡ A) → H v → H (Val-subst pA v)
  H-subst b.refl h = h

  H-unsubst :
    ∀ {tA A : Type (b.suc n)}{a : Tm · (λ _ → tA)}{v : Val D a} →
    (pA : tA ≡ A) → H (Val-subst pA v) → H v
  H-unsubst b.refl h = h

  -- c halts at the current frame with a halting value
  Halts : Config D → Set₁
  Halts c = HaltsWith c H

  {- The halting relation on environments and stacks -}

  Hᵉ : ∀ {Γ : Con}{sΓ : Ctx Γ len}{env : Env D len}{δ : Sub · Γ} →
    env ⊨ sΓ as δ → Set₁
  Hᵉ nil = b.⊤
  Hᵉ (cons {v = v} pf pA) = Hᵉ pf × H v

  Hˢ : ∀ {Γ : Con}{sΓ : Ctx Γ len}{env : Env D len}{δ : Sub · Γ}
    {wf : env ⊨ sΓ as δ}{st : Env D ns}{σ : Stack Γ ns} →
    wf ⊢ st ⊨ˢ σ → Set₁
  Hˢ nil = b.⊤
  Hˢ (cons {v = v} pf ptt eq) = Hˢ pf × H v

  {- Access lemmas -}

  Hᵉ-find :
    ∀ {Γ : Con}{sΓ : Ctx Γ len}{env : Env D len}{δ : Sub · Γ}
      {A : Ty Γ n} →
    (wf : env ⊨ sΓ as δ) → Hᵉ wf → (x : V sΓ A) → H (findᵉ env x wf)
  Hᵉ-find (cons pf b.refl) (h b., hv) vz = hv
  Hᵉ-find (cons pf pA) (h b., hv) (vs x) = Hᵉ-find pf h x

  Hˢ-find :
    ∀ {Γ : Con}{sΓ : Ctx Γ len}{env : Env D len}{δ : Sub · Γ}
      {wf : env ⊨ sΓ as δ}{st : Env D ns}{σ : Stack Γ ns}{A : Ty Γ n} →
    (wf-st : wf ⊢ st ⊨ˢ σ) → Hˢ wf-st → (x : SVar σ A) → H (findˢ st x wf-st)
  Hˢ-find (cons pf b.refl b.refl) (h b., hv) vz = hv
  Hˢ-find (cons pf ptt eq) (h b., hv) (vs x) = Hˢ-find pf h x

  Hˢ-take :
    ∀ {Γ : Con}{sΓ : Ctx Γ len}{env : Env D len}{δ : Sub · Γ}
      {wf : env ⊨ sΓ as δ}{st : Env D (m b.+ n)}{σ : Stack Γ (m b.+ n)} →
    (wf-st : wf ⊢ st ⊨ˢ σ) → Hˢ wf-st → Hˢ (⊨ˢ-take {m = m} wf-st)
  Hˢ-take {m = b.zero} wf-st h = b.tt
  Hˢ-take {m = b.suc m} (cons pf ptt eq) (h b., hv) = Hˢ-take pf h b., hv

  Hˢ-drop :
    ∀ {Γ : Con}{sΓ : Ctx Γ len}{env : Env D len}{δ : Sub · Γ}
      {wf : env ⊨ sΓ as δ}{st : Env D (m b.+ n)}{σ : Stack Γ (m b.+ n)} →
    (wf-st : wf ⊢ st ⊨ˢ σ) → Hˢ wf-st → Hˢ (⊨ˢ-drop {m = m} wf-st)
  Hˢ-drop {m = b.zero} wf-st h = h
  Hˢ-drop {m = b.suc m} (cons pf ptt eq) (h b., hv) = Hˢ-drop pf h

  -- A halting stack viewed as an environment is a halting environment
  Hᵉ-clo⊨ :
    ∀ {Γ : Con}{sΓ : Ctx Γ len}{env : Env D len}{Δ : Con}{δ : Sub · Γ}{η : Sub Γ Δ}
      {sΔ : Ctx Δ ns}{st : Env D ns}{σ : Stack Γ ns} →
    (wf : env ⊨ sΓ as δ) → (wf-st : wf ⊢ st ⊨ˢ σ) → Hˢ wf-st →
    (pf : sΓ ⊢ σ of sΔ as η) → Hᵉ (clo⊨ wf wf-st pf)
  Hᵉ-clo⊨ {sΔ = ◆} {◆} {◆} wf nil h nil = b.tt
  Hᵉ-clo⊨ {sΔ = sΔ ∷ A} {st ∷ v} {σ ∷ t} wf (cons wf-st b.refl b.refl) (h b., hv) (cons ⦃ pf ⦄) =
    Hᵉ-clo⊨ wf wf-st h pf b., hv

  -- A label definition is halting if every closure formed from it with a halting
  -- environment is in the halting relation.
  H-Pi : ∀ {Γ len n}{sΓ : Ctx Γ len}{A : Ty Γ n}{B : Ty (Γ ▹ A) n} →
    Pi D id sΓ A B → Set₁
  H-Pi {sΓ = sΓ} L =
    ∀ {env' : Env D _}{δ' : Sub · _} (wf-env' : env' ⊨ sΓ as δ') →
    Hᵉ wf-env' → H (clo L env' ⦃ wf-env' ⦄)

  H-Is : ∀ {Γ : Con}{sΓ : Ctx Γ len}{σ : Stack Γ ms}{σ' : Stack Γ ns} → Is D sΓ σ σ' → Set₁
  H-Is RET = b.⊤
  H-Is (CLO ns L >> ins) = H-Pi L × H-Is ins
  H-Is (CLOENV L >> ins) = H-Pi L × H-Is ins
  H-Is (ITER P Z S >> ins) = H-Pi Z × H-Pi S × H-Is ins
  H-Is (_ >> ins) = H-Is ins 

  H-Pi⇒H-Is : 
    ∀ {Γ : Con}{sΓ : Ctx Γ len}{σ : Stack Γ ms}{σ' : Stack Γ ns} → 
      (∀ {id Γ len n}{sΓ : Ctx Γ len}{A : Ty Γ n}{B : Ty (Γ ▹ A) n} (L : Pi D id sΓ A B) → H-Pi L) → 
      (ins : Is D sΓ σ σ') → H-Is ins
  H-Pi⇒H-Is f RET = b.tt
  H-Pi⇒H-Is f (CLO ns L >> ins) = f L b., H-Pi⇒H-Is f ins
  H-Pi⇒H-Is f (CLOENV L >> ins) = f L b., H-Pi⇒H-Is f ins
  H-Pi⇒H-Is f (ITER P Z S >> ins) = f Z b., f S b., H-Pi⇒H-Is f ins
  H-Pi⇒H-Is f (NOP >> ins) = H-Pi⇒H-Is f ins
  H-Pi⇒H-Is f (VAR x >> ins) = H-Pi⇒H-Is f ins
  H-Pi⇒H-Is f (POP >> ins) = H-Pi⇒H-Is f ins
  H-Pi⇒H-Is f (APP >> ins) = H-Pi⇒H-Is f ins
  H-Pi⇒H-Is f (LIT n >> ins) = H-Pi⇒H-Is f ins
  H-Pi⇒H-Is f (TY A >> ins) = H-Pi⇒H-Is f ins
  H-Pi⇒H-Is f (SWP >> ins) = H-Pi⇒H-Is f ins
  H-Pi⇒H-Is f (ST x >> ins) = H-Pi⇒H-Is f ins
  H-Pi⇒H-Is f (INC >> ins) = H-Pi⇒H-Is f ins
  H-Pi⇒H-Is f (UNIT >> ins) = H-Pi⇒H-Is f ins
  H-Pi⇒H-Is f (PAIR >> ins) = H-Pi⇒H-Is f ins
  H-Pi⇒H-Is f (FST >> ins) = H-Pi⇒H-Is f ins
  H-Pi⇒H-Is f (SND >> ins) = H-Pi⇒H-Is f ins
  H-Pi⇒H-Is f (UP >> ins) = H-Pi⇒H-Is f ins
  H-Pi⇒H-Is f (DOWN >> ins) = H-Pi⇒H-Is f ins

{-
  Instr-ok-map : ∀ {Γ : Con}{sΓ : Ctx Γ len}{σ : Stack Γ ms}{σ' : Stack Γ ns}
    (∀ {id' Γ len n}{sΓ : Ctx Γ len}{A : Ty Γ n}{B : Ty (Γ ▹ A) n} (L : Pi D id' sΓ A B) → id' < id → H-Is (Proc.instr (I L))) → 
    (i : Instr D sΓ σ σ') → H-Is i
  Instr-ok-map f (CLO ns L) p = f L p
  Instr-ok-map f (CLOENV L) p = f L p
  Instr-ok-map f (ITER Q Z S) (pz b., ps) = f Z pz b., f S ps
  Instr-ok-map f NOP p = tt₁
  Instr-ok-map f (VAR x) p = tt₁
  Instr-ok-map f POP p = tt₁
  Instr-ok-map f APP p = tt₁
  Instr-ok-map f (LIT k) p = tt₁
  Instr-ok-map f (TY A) p = tt₁
  Instr-ok-map f SWP p = tt₁
  Instr-ok-map f (ST x) p = tt₁
  Instr-ok-map f INC p = tt₁
  Instr-ok-map f UNIT p = tt₁
  Instr-ok-map f PAIR p = tt₁
  Instr-ok-map f FST p = tt₁
  Instr-ok-map f SND p = tt₁
  Instr-ok-map f UP p = tt₁
  Instr-ok-map f DOWN p = tt₁

  Is-ok-map : ∀ {Γ : Con}{sΓ : Ctx Γ len}{σ : Stack Γ ms}{σ' : Stack Γ ns}
    {P Q : LabelPred} → (∀ {id Γ len n}{sΓ : Ctx Γ len}{A : Ty Γ n}{B : Ty (Γ ▹ A) n}
    (L : Pi D id sΓ A B) → P L → Q L) → (ins : Is D sΓ σ σ') → Is-ok P ins → Is-ok Q ins
  Is-ok-map f RET p = tt₁
  Is-ok-map f (i >> ins) (p b., ps) = Instr-ok-map f i p b., Is-ok-map f ins ps

  Instr-ok-all : ∀ {Γ : Con}{sΓ : Ctx Γ len}{σ : Stack Γ ms}{σ' : Stack Γ ns}
    {P : LabelPred} → (∀ {id Γ len n}{sΓ : Ctx Γ len}{A : Ty Γ n}{B : Ty (Γ ▹ A) n}
    (L : Pi D id sΓ A B) → P L) → (i : Instr D sΓ σ σ') → Instr-ok P i
  Instr-ok-all f (CLO ns L) = f L
  Instr-ok-all f (CLOENV L) = f L
  Instr-ok-all f (ITER Q Z S) = f Z b., f S
  Instr-ok-all f NOP = tt₁
  Instr-ok-all f (VAR x) = tt₁
  Instr-ok-all f POP = tt₁
  Instr-ok-all f APP = tt₁
  Instr-ok-all f (LIT k) = tt₁
  Instr-ok-all f (TY A) = tt₁
  Instr-ok-all f SWP = tt₁
  Instr-ok-all f (ST x) = tt₁
  Instr-ok-all f INC = tt₁
  Instr-ok-all f UNIT = tt₁
  Instr-ok-all f PAIR = tt₁
  Instr-ok-all f FST = tt₁
  Instr-ok-all f SND = tt₁
  Instr-ok-all f UP = tt₁
  Instr-ok-all f DOWN = tt₁
-}

