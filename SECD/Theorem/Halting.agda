module SECD.Theorem.Halting where

open import Agda.Primitive using (lzero; lsuc)
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

open b using (ℕ; _≡_; _×_)

private variable
  m n len ms ns lf : ℕ

-- Concatenation of reduction sequences
infixr 20 _++*_
_++*_ : ∀{c c' c'' : Config} → c ↝* c' → c' ↝* c'' → c ↝* c''
■ ++* tr = tr
(s ⟫ tr) ++* tr' = s ⟫ (tr ++* tr')

-- Transporting a value along an equation between closed types
Val-subst :
  ∀ {tA A : Type (b.suc n)}{a : Tm · (λ _ → tA)} →
  (pA : tA ≡ A) → Val a → Val (Tm-subst a pA)
Val-subst b.refl v = v

{- Halting at the current frame -}

-- [c ↓ v] : the configuration c reduces to a RET configuration whose
-- stack of call frames is that of c, whose abstract return value and
-- closing substitution are those of c, and whose top stack value is v.
-- (Within a frame, the code, environment, closing substitution and the
-- final abstract value never change, so this is the only sensible notion
-- of "halting at the current frame".)
data _↓_ (c : Config) : Val (Config.t' c [ Config.δ c ]) → Set₁ where
  halt :
    ∀ {σ : Stack (Config.Δ c) ns}
      {env : Env (Config.len c)}
      {st : Env ns}
      {v : Val (Config.t' c [ Config.δ c ])}
      {wf-env : env ⊨ Config.sΔ c as Config.δ c}
      {wf-st : wf-env ⊢ st ⊨ˢ σ}
      {eq-A : Config.A' c [ Config.δ c ]T ≡ Config.A c [ Config.η c ]T}
      {eq-t : Config.s c [ Config.η c ] ≡ Tm-subst (Config.t' c [ Config.δ c ]) (b.cong-app eq-A)} →
    c ↝* conf (RET {σ = σ ∷ Config.t' c}) env (st ∷ v) (Config.sf c)
              wf-env (cons wf-st b.refl b.refl) eq-A eq-t →
    ----------------------------------------------------------------
    c ↓ v

-- c halts at the current frame with a value satisfying P
record HaltsWith (c : Config) (P : Val (Config.t' c [ Config.δ c ]) → Set₁) : Set₁ where
  constructor halts
  field
    val : Val (Config.t' c [ Config.δ c ])
    trace : c ↓ val
    good : P val

{- The halting relation on values -}

-- Π-case: v is a closure, and running its code on any halting argument
-- halts at the current frame (for every frame stack) with a halting result.
HΠ :
  ∀ {A : Type (b.suc n)}{B : ⟦ uni (Type n) ⟦_⟧ ~~ A ⟧ → Type (b.suc n)}
    (HA : ∀ {a : Tm · (λ _ → A)} → Val a → Set₁)
    (HB : ∀ (x : ⟦ uni (Type n) ⟦_⟧ ~~ A ⟧){b : Tm · (λ _ → B x)} → Val b → Set₁)
    {f : Tm · (λ _ → `Π A B)} →
  Val f → Set₁
HΠ HA HB (clo {A = A₁} {B = B₁} {δ = δ'} {t = t} env' ins ⦃ wf-env' ⦄) =
  ∀ {tA : Type (b.suc _)}{a : Tm · (λ _ → tA)}
    (v : Val a) (pA : tA ≡ (A₁ [ δ' ]T) b.tt) → HA (Val-subst pA v) →
  ∀ {Γ : Con}{A₀ : Ty Γ _}{s : Tm Γ A₀}{η : Sub · Γ}{lf}
    (sf : Sf s η lf)
    (eq-A : B₁ [ δ' ▻ Tm-subst a pA ]T ≡ A₀ [ η ]T)
    (eq-t : s [ η ] ≡ Tm-subst (t [ δ' ▻ Tm-subst a pA ]) (b.cong-app eq-A)) →
  HaltsWith (conf ins (env' ∷ v) ◆ sf (cons wf-env' pA) nil eq-A eq-t)
            (HB (Tm-subst a pA ~$ b.tt))

-- Σ-case: both components halt.
HΣ :
  ∀ {A : Type (b.suc n)}{B : ⟦ uni (Type n) ⟦_⟧ ~~ A ⟧ → Type (b.suc n)}
    (HA : ∀ {a : Tm · (λ _ → A)} → Val a → Set₁)
    (HB : ∀ (x : ⟦ uni (Type n) ⟦_⟧ ~~ A ⟧){b : Tm · (λ _ → B x)} → Val b → Set₁)
    {p : Tm · (λ _ → `Σ A B)} →
  Val p → Set₁
HΣ HA HB (pair {t = t₁} v₁ v₂) = HA v₁ × HB (t₁ ~$ b.tt) v₂

-- Lifting case: the underlying value halts.
H↑ :
  ∀ {A : Type (b.suc n)}
    (HA : ∀ {a : Tm · (λ _ → A)} → Val a → Set₁)
    {t : Tm · (λ _ → `↑ A)} →
  Val t → Set₁
H↑ HA (lift v) = HA v

-- The halting relation, by recursion on the code of the closed type.
-- Base types, universes and identity types: every well-typed value halts.
H : ∀ {n} {A : Type (b.suc n)} {t : Tm · (λ _ → A)} → Val t → Set₁
H {A = `N} v = ⊤₁
H {A = `B} v = ⊤₁
H {A = `⊤} v = ⊤₁
H {A = `⊥} v = ⊤₁
H {A = `U} v = ⊤₁
H {A = `Id A x y} v = ⊤₁
H {A = `Π A B} v = HΠ (H {A = A}) (λ x → H {A = B x}) v
H {A = `Σ A B} v = HΣ (H {A = A}) (λ x → H {A = B x}) v
H {n = b.zero} {A = `↑ ()} v
H {n = b.suc n} {A = `↑ A} v = H↑ (H {A = A}) v

-- Halting is invariant under transport along type equations
H-subst :
  ∀ {tA A : Type (b.suc n)}{a : Tm · (λ _ → tA)}{v : Val a} →
  (pA : tA ≡ A) → H v → H (Val-subst pA v)
H-subst b.refl h = h

H-unsubst :
  ∀ {tA A : Type (b.suc n)}{a : Tm · (λ _ → tA)}{v : Val a} →
  (pA : tA ≡ A) → H (Val-subst pA v) → H v
H-unsubst b.refl h = h

-- c halts at the current frame with a halting value
Halts : Config → Set₁
Halts c = HaltsWith c H

{- The halting relation on environments and stacks -}

Hᵉ : ∀ {Γ : Con}{sΓ : Ctx Γ len}{env : Env len}{δ : Sub · Γ} →
  env ⊨ sΓ as δ → Set₁
Hᵉ nil = ⊤₁
Hᵉ (cons {v = v} pf pA) = Hᵉ pf × H v

Hˢ : ∀ {Γ : Con}{sΓ : Ctx Γ len}{env : Env len}{δ : Sub · Γ}
  {wf : env ⊨ sΓ as δ}{st : Env ns}{σ : Stack Γ ns} →
  wf ⊢ st ⊨ˢ σ → Set₁
Hˢ nil = ⊤₁
Hˢ (cons {v = v} pf ptt eq) = Hˢ pf × H v

{- Access lemmas -}

Hᵉ-find :
  ∀ {Γ : Con}{sΓ : Ctx Γ len}{env : Env len}{δ : Sub · Γ}
    {A : Ty Γ n} →
  (wf : env ⊨ sΓ as δ) → Hᵉ wf → (x : V sΓ A) → H (findᵉ env x wf)
Hᵉ-find (cons pf b.refl) (h b., hv) vz = hv
Hᵉ-find (cons pf pA) (h b., hv) (vs x) = Hᵉ-find pf h x

Hˢ-find :
  ∀ {Γ : Con}{sΓ : Ctx Γ len}{env : Env len}{δ : Sub · Γ}
    {wf : env ⊨ sΓ as δ}{st : Env ns}{σ : Stack Γ ns}{A : Ty Γ n} →
  (wf-st : wf ⊢ st ⊨ˢ σ) → Hˢ wf-st → (x : SVar σ A) → H (findˢ st x wf-st)
Hˢ-find (cons pf b.refl b.refl) (h b., hv) vz = hv
Hˢ-find (cons pf ptt eq) (h b., hv) (vs x) = Hˢ-find pf h x

Hˢ-take :
  ∀ {Γ : Con}{sΓ : Ctx Γ len}{env : Env len}{δ : Sub · Γ}
    {wf : env ⊨ sΓ as δ}{st : Env (m b.+ n)}{σ : Stack Γ (m b.+ n)} →
  (wf-st : wf ⊢ st ⊨ˢ σ) → Hˢ wf-st → Hˢ (⊨ˢ-take {m = m} wf-st)
Hˢ-take {m = b.zero} wf-st h = tt₁
Hˢ-take {m = b.suc m} (cons pf ptt eq) (h b., hv) = Hˢ-take pf h b., hv

Hˢ-drop :
  ∀ {Γ : Con}{sΓ : Ctx Γ len}{env : Env len}{δ : Sub · Γ}
    {wf : env ⊨ sΓ as δ}{st : Env (m b.+ n)}{σ : Stack Γ (m b.+ n)} →
  (wf-st : wf ⊢ st ⊨ˢ σ) → Hˢ wf-st → Hˢ (⊨ˢ-drop {m = m} wf-st)
Hˢ-drop {m = b.zero} wf-st h = h
Hˢ-drop {m = b.suc m} (cons pf ptt eq) (h b., hv) = Hˢ-drop pf h

-- A halting stack viewed as an environment is a halting environment
Hᵉ-clo⊨ :
  ∀ {Γ : Con}{sΓ : Ctx Γ len}{env : Env len}{Δ : Con}{δ : Sub · Γ}{η : Sub Γ Δ}
    {sΔ : Ctx Δ ns}{st : Env ns}{σ : Stack Γ ns} →
  (wf : env ⊨ sΓ as δ) → (wf-st : wf ⊢ st ⊨ˢ σ) → Hˢ wf-st →
  (pf : sΓ ⊢ σ of sΔ as η) → Hᵉ (clo⊨ wf wf-st pf)
Hᵉ-clo⊨ {sΔ = ◆} {◆} {◆} wf nil h nil = tt₁
Hᵉ-clo⊨ {sΔ = sΔ ∷ A} {st ∷ v} {σ ∷ t} wf (cons wf-st b.refl b.refl) (h b., hv) (cons ⦃ pf ⦄) =
  Hᵉ-clo⊨ wf wf-st h pf b., hv
