module Machine.App where

import Lib.Basic as b
open import Lib.Order

open import Model.Universe
open import Model.Shallow
open import Model.Context
open import Model.Labels
open import Model.Stack

open import Machine.Value
open import Machine.Config

open b using (ℕ; _+_)
open LCon

open ~Π

private variable
  m n len len' ms ms' ns ns' lf d d' id : ℕ

lemma : 
  ∀ {Δ : Con}{A : Ty Δ n}{δ : Sub · Δ}{a : Tm Δ A} → 
    {A' : Code (uni (Type n) ⟦_⟧)} →
  (pf : A' b.≡ A (δ b.tt)) → 
  b.subst (⟦_⟧ {n = b.suc n}) pf (b.subst (⟦_⟧ {n = b.suc n}) (b.sym pf) (a .~fun (δ b.tt))) b.≡ a .~fun (δ b.tt)
lemma {A = A} {δ} b.refl = b.refl

lemma2 : 
  ∀ {Δ : Con}{A : Ty Δ n}{B : Ty (Δ ▹ A) n}{δ : Sub · Δ}
    {f : Tm Δ (Π A B)}{a : Tm Δ A}
    {A' : Code (uni (Type n) ⟦_⟧)}
    {B' : ⟦ (uni (Type n) ⟦_⟧) ~~ A' ⟧ → Code (uni (Type n) ⟦_⟧)} →
    {f' : Tm · (λ _ → `Π A' B')}
    (pA : `Π A' B' b.≡ `Π (A (δ b.tt)) (λ x → B (δ b.tt ~, x))) →
    (ptf : f [ δ ] b.≡ Tm-subst f' pA) →     
    {t : Tm · (λ _ → B' (Tm-subst (a [ δ ]) (b.sym (inj₁ pA)) .~fun b.tt))} → 
    (eq : (f' $ Tm-subst (a [ δ ]) (b.sym (inj₁ pA))) b.≡ t) → 
    ((f $ a) [ δ ]) b.≡ 
      Tm-subst t 
        (b.cong-app (b.ext-tt (inj₂ pA (lemma {Δ = Δ} {A} {δ} {a} (inj₁ pA)))))
lemma2 b.refl b.refl b.refl = b.refl

app-rule :
    {D : LCon}
    (I : Impl D)
    {Γ Δ : Con}
    {sΓ : Ctx Γ len}
    {sΔ : Ctx Δ len'}
    {A : Ty Γ n}
    {s : Tm Γ A}
    {η : Sub · Γ}
    {σ : Stack Δ ms}
    {σ' : Stack Δ ns}
    {A' : Ty Δ n}
    {t' : Tm Δ A'}
    ----
    {A'' : Ty Δ m}
    {B'' : Ty (Δ ▹ A'') m}
    {f : Tm Δ (Π A'' B'')}
    {a : Tm Δ A''}
    ----
    {ins : Is D sΔ d (σ ∷ (f $ a)) (σ' ∷ t')}
    {env : Env D len'}
    {st : Env D ms}
    {sf : Sf D s η lf}
    ----
    {δ : Sub · Δ}
    {wf-env : env ⊨ sΔ as δ}
    {wf-st : wf-env ⊢ st ⊨ˢ σ}
    {eq-A : A' [ δ ]T b.≡ A [ η ]T}
    {eq-t : s [ η ] b.≡ Tm-subst (t' [ δ ]) (b.cong-app eq-A)}
    ----
    {Δ' : Con}
    {sΔ' : Ctx Δ' ms'}
    {δ' : Sub · Δ'}
    {A+ : Ty Δ' m}
    {B+ : Ty (Δ' ▹ A+) m}
    {L : Pi D id sΔ' A+ B+}
    {env' : Env D ms'}
    {wf-env' : env' ⊨ sΔ' as δ'}
    {ρ : Sub Δ Δ'}
    {pf : env' ⊨ sΔ' as δ'} 
    ----
    {pA :  ((Π A+ B+) [ δ' ]T) b.≡ ((Π A'' B'') [ δ ]T)}
    {ptf : f [ δ ] b.≡ Tm-subst (lapp D L δ') (b.cong-app pA)}
    {v : Val D (a [ δ ])} → 
    Config D
app-rule {D = D} I 
  {A'' = A''} {B''} {f} {a}
  {ins = ins} {env} {st} {sf} {δ} {wf-env} {wf-st} {eq-A} {eq-t} 
  {L = L} {env'} {wf-env'} {ρ} {pf} {pA} {ptf} {v}
  = 
    let eq-A' = (b.sym (inj₁ (b.cong-app pA))) in
    conf (Proc.instr (I L)) (env' ∷ v) ◆ (sf ∷ fr ins env st wf-env wf-st eq-A eq-t) 
    (cons wf-env' eq-A') nil 
    (b.ext-tt (inj₂ (b.cong-app pA) (lemma {A = A''} {δ} {a} (inj₁ (b.cong-app pA))))) 
    (lemma2 {f = f} {a = a} (b.cong-app pA) ptf (lapp-β D))

   