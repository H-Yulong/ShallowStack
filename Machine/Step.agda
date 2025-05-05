module Machine.Step where

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

private variable
  m n m' len len' ms ms' ns ns' lf d d' id : ℕ

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

-- TODO: too many implicit variables!
-- Refactor to hide things under some abstraction!



-- This intrinsic definition means we have preservation   
data _⊢_↝_ {D : LCon} (I : Impl D) : Config D → Config D → Set₁ where
  C-NOP : 
    {Γ Δ : Con}
    {sΔ : Ctx Δ len'}
    {A : Ty Γ n}
    {s : Tm Γ A}
    {η : Sub · Γ}
    {σ : Stack Δ ms}
    {σ' : Stack Δ ns}
    {A' : Ty Δ n}
    {t' : Tm Δ A'}
    ----
    {ins : Is D sΔ d σ (σ' ∷ t')}
    {env : Env D len'}
    {st : Env D ms}
    {sf : Sf D s η lf}
    ----
    {δ : Sub · Δ}
    {wf-env : env ⊨ sΔ as δ}
    {wf-st : wf-env ⊢ st ⊨ˢ σ}
    {eq-A : A' [ δ ]T b.≡ A [ η ]T}
    {eq-t : s [ η ] b.≡ Tm-subst (t' [ δ ]) (b.cong-app eq-A)} →  
    ---------------------------------------- 
    I ⊢ (conf (NOP >> ins) env st sf wf-env wf-st eq-A eq-t)
      ↝ (conf ins env st sf wf-env wf-st eq-A eq-t)
  --
  C-VAR :     
    {Γ Δ : Con}
    {sΔ : Ctx Δ len'}
    {A : Ty Γ n}
    {s : Tm Γ A}
    {η : Sub · Γ}
    {σ : Stack Δ ms}
    {σ' : Stack Δ ns}
    {A' : Ty Δ n}
    {t' : Tm Δ A'}
    ----
    {B : Ty Δ m}
    {x : V sΔ B}
    {ins : Is D sΔ d (σ ∷ ⟦ x ⟧V) (σ' ∷ t')}
    {env : Env D len'}
    {st : Env D ms}
    {sf : Sf D s η lf}
    ----
    {δ : Sub · Δ}
    {wf-env : env ⊨ sΔ as δ}
    {wf-st : wf-env ⊢ st ⊨ˢ σ}
    {eq-A : A' [ δ ]T b.≡ A [ η ]T}
    {eq-t : s [ η ] b.≡ Tm-subst (t' [ δ ]) (b.cong-app eq-A)} →  
    ----------------------------
    I ⊢ (conf (VAR x >> ins) env st sf wf-env wf-st eq-A eq-t) 
      ↝ (conf ins env (st ∷ findᵉ env x wf-env) sf wf-env (cons wf-st b.refl b.refl) eq-A eq-t)
  --
  C-ST :
    {Γ Δ : Con}
    {sΔ : Ctx Δ len'}
    {A : Ty Γ n}
    {s : Tm Γ A}
    {η : Sub · Γ}
    {σ : Stack Δ ms}
    {σ' : Stack Δ ns}
    {A' : Ty Δ n}
    {t' : Tm Δ A'}
    ----
    {B : Ty Δ m}
    {x : SVar σ B}
    {ins : Is D sΔ d (σ ∷ find σ x) (σ' ∷ t')}
    {env : Env D len'}
    {st : Env D ms}
    {sf : Sf D s η lf}
    ----
    {δ : Sub · Δ}
    {wf-env : env ⊨ sΔ as δ}
    {wf-st : wf-env ⊢ st ⊨ˢ σ}
    {eq-A : A' [ δ ]T b.≡ A [ η ]T}
    {eq-t : s [ η ] b.≡ Tm-subst (t' [ δ ]) (b.cong-app eq-A)} →   
    --------------------------------------
    I ⊢ conf (ST x >> ins) env st sf wf-env wf-st eq-A eq-t
      ↝ conf ins env (st ∷ findˢ st x wf-st) sf wf-env (cons wf-st b.refl b.refl) eq-A eq-t
  --
  C-CLO : 
    {Γ Δ : Con}
    {sΔ : Ctx Δ len'}
    {A : Ty Γ m}
    {s : Tm Γ A}
    {η : Sub · Γ}
    {σ : Stack Δ (ms' + ms)}
    {σ' : Stack Δ ns}
    {A' : Ty Δ m}
    {t' : Tm Δ A'}
    ----
    {Δ' : Con}
    {sΔ' : Ctx Δ' ms'}
    {A'' : Ty Δ' n}
    {B'' : Ty (Δ' ▹ A'') n}
    {L : Pi D id sΔ' A'' B''}
    {ρ : Sub Δ Δ'}
    ----
    {ins : Is D sΔ d (drop ms' σ ∷ lapp D L ρ) (σ' ∷ t')}
    {env : Env D len'}
    {st : Env D (ms' + ms)}
    {sf : Sf D s η lf}
    ----
    {δ : Sub · Δ}
    {wf-env : env ⊨ sΔ as δ}
    {wf-st : wf-env ⊢ st ⊨ˢ σ}
    {eq-A : A' [ δ ]T b.≡ A [ η ]T}
    {eq-t : s [ η ] b.≡ Tm-subst (t' [ δ ]) (b.cong-app eq-A)} → 
    ----
    ⦃ pf : sΔ ⊢ (take ms' σ) of sΔ' as ρ ⦄ →
    ⦃ bound : id < d ⦄ → 
    ------------------------------ 
    let closure = clo L (takeᵉ ms' st) ⦃ clo⊨ wf-env (⊨ˢ-take wf-st) pf ⦄ in
    let wf-st' = cons (⊨ˢ-drop wf-st) b.refl (lapp[] D) in
    I ⊢ conf (CLO ms' L >> ins) env st sf wf-env wf-st eq-A eq-t 
      ↝ conf ins env ((dropᵉ ms' st) ∷ closure) sf wf-env wf-st' eq-A eq-t
  C-APP : 
    {Γ Δ : Con}
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
    ----
    {pA :  ((Π A+ B+) [ δ' ]T) b.≡ ((Π A'' B'') [ δ ]T)}
    {ptf : f [ δ ] b.≡ Tm-subst (lapp D L δ') (b.cong-app pA)}
    {v : Val D (a [ δ ])} → 
    ------------------------------
    let new-fr = fr ins env st wf-env wf-st eq-A eq-t in
    let eq-A' = b.sym (inj₁ (b.cong-app pA)) in
    I ⊢ conf (APP {f = f} >> ins) env (st ∷ clo L env' ⦃ wf-env' ⦄ ∷ v) sf wf-env (cons (cons wf-st (b.cong-app pA) ptf) b.refl b.refl) eq-A eq-t 
      ↝ conf (Proc.instr (I L)) (env' ∷ v) ◆ (sf ∷ new-fr) (cons wf-env' eq-A') nil 
        (b.ext-tt (inj₂ (b.cong-app pA) (lemma {A = A''} {δ} {a} (inj₁ (b.cong-app pA))))) 
        (lemma2 {f = f} {a = a} (b.cong-app pA) ptf (lapp-β D))
  --
  C-RET :
      {Δ' Δ : Con}
      {sΔ : Ctx Δ len}
      {sΔ' : Ctx Δ' len'}
      ----
      {σ : Stack Δ ms}
      {A' : Ty Δ n}
      {t' : Tm Δ A'}
      ----
      {θ : Stack Δ' ms'}
      {θ' : Stack Δ' ns'}
      {B : Ty Δ' n}
      {B' : Ty Δ' m}
      {s : Tm Δ' B}
      {s' : Tm Δ' B'}
      {ins : Is D sΔ' d' (θ ∷ s) (θ' ∷ s')}
      {env' : Env D len'}
      {st' : Env D ms'}
      ----
      {δ' : Sub · Δ'}
      {wf-env' : env' ⊨ sΔ' as δ'}
      {wf-st' : wf-env' ⊢ st' ⊨ˢ θ}
      ----
        {Γ : Con}
        {A : Ty Γ m}
        {r : Tm Γ A}
        {η : Sub · Γ}
      {eq-A' : B' [ δ' ]T b.≡ A [ η ]T}
      {eq-t' : r [ η ] b.≡ Tm-subst (s' [ δ' ]) (b.cong-app eq-A')}
      ----
      {env : Env D len}
      {st : Env D ms}
      {sf : Sf D r η lf}
      ----
      {δ : Sub · Δ}
      {wf-env : env ⊨ sΔ as δ}
      {wf-st : wf-env ⊢ st ⊨ˢ σ}
      {eq-A : A' [ δ ]T b.≡ B [ δ' ]T}
      {eq-t : s [ δ' ] b.≡ Tm-subst (t' [ δ ]) (b.cong-app eq-A)}
      ----
      {v : Val D (t' [ δ ])} → 
    ------------------------------
    let new-fr = fr ins env' st' wf-env' wf-st' eq-A' eq-t' in
    I ⊢ conf (RET {d = d} {σ = σ ∷ t'}) env (st ∷ v) (sf ∷ new-fr) wf-env (cons wf-st b.refl b.refl) eq-A eq-t
      ↝ conf ins env' (st' ∷ v) sf wf-env' (cons wf-st' (b.cong-app eq-A) eq-t) eq-A' eq-t'
  --
  C-TLIT : 
    {Γ Δ : Con}
    {sΔ : Ctx Δ len'}
    {A : Ty Γ n}
    {s : Tm Γ A}
    {η : Sub · Γ}
    {σ : Stack Δ ms}
    {σ' : Stack Δ ns}
    {A' : Ty Δ n}
    {t' : Tm Δ A'}
    ----
    {B : Ty Δ m}
    {ins : Is D sΔ d (σ ∷ (c B)) (σ' ∷ t')}
    {env : Env D len'}
    {st : Env D ms}
    {sf : Sf D s η lf}
    ----
    {δ : Sub · Δ}
    {wf-env : env ⊨ sΔ as δ}
    {wf-st : wf-env ⊢ st ⊨ˢ σ}
    {eq-A : A' [ δ ]T b.≡ A [ η ]T}
    {eq-t : s [ η ] b.≡ Tm-subst (t' [ δ ]) (b.cong-app eq-A)} →  
    ----------------------------
    I ⊢ (conf (TLIT B >> ins) env st sf wf-env wf-st eq-A eq-t) 
    ↝ (conf ins env (st ∷ ty (B [ δ ]T)) sf wf-env (cons wf-st b.refl b.refl) eq-A eq-t)   
  -- 
  C-LIT : 
    {Γ Δ : Con}
    {sΔ : Ctx Δ len'}
    {A : Ty Γ n}
    {s : Tm Γ A}
    {η : Sub · Γ}
    {σ : Stack Δ ms}
    {σ' : Stack Δ ns}
    {A' : Ty Δ n}
    {t' : Tm Δ A'}
    ----
    {k : ℕ}
    {ins : Is D sΔ d (σ ∷ (nat k)) (σ' ∷ t')}
    {env : Env D len'}
    {st : Env D ms}
    {sf : Sf D s η lf}
    ----
    {δ : Sub · Δ}
    {wf-env : env ⊨ sΔ as δ}
    {wf-st : wf-env ⊢ st ⊨ˢ σ}
    {eq-A : A' [ δ ]T b.≡ A [ η ]T}
    {eq-t : s [ η ] b.≡ Tm-subst (t' [ δ ]) (b.cong-app eq-A)} →  
    ----------------------------
    I ⊢ (conf (LIT k >> ins) env st sf wf-env wf-st eq-A eq-t) 
      ↝ (conf ins env (st ∷ lit-n k) sf wf-env (cons wf-st b.refl b.refl) eq-A eq-t)      
  --
  C-SWP : 
    {Γ Δ : Con}
    {sΔ : Ctx Δ len'}
    {A : Ty Γ n}
    {s : Tm Γ A}
    {η : Sub · Γ}
    {σ : Stack Δ ms}
    {σ' : Stack Δ ns}
    {A' : Ty Δ n}
    {t' : Tm Δ A'}
    ----
    {B1 : Ty Δ m}
    {t1 : Tm Δ B1}
    {B2 : Ty Δ m'}
    {t2 : Tm Δ B2}
    {ins : Is D sΔ d (σ ∷ t2 ∷ t1) (σ' ∷ t')}
    {env : Env D len'}
    {st : Env D ms}
    {sf : Sf D s η lf}
    ----
    {δ : Sub · Δ}
    {v1 : Val D (t1 [ δ ])}
    {v2 : Val D (t2 [ δ ])}
    {wf-env : env ⊨ sΔ as δ}
    {wf-st : wf-env ⊢ st ⊨ˢ σ}
    {eq-A : A' [ δ ]T b.≡ A [ η ]T}
    {eq-t : s [ η ] b.≡ Tm-subst (t' [ δ ]) (b.cong-app eq-A)} →  
    ----------------------------
    let wf-st1 = cons (cons wf-st b.refl b.refl) b.refl b.refl in
    let wf-st2 = cons (cons wf-st b.refl b.refl) b.refl b.refl in 
    I ⊢ (conf (SWP >> ins) env (st ∷ v1 ∷ v2) sf wf-env wf-st1 eq-A eq-t) 
      ↝ (conf ins env (st ∷ v2 ∷ v1) sf wf-env wf-st2 eq-A eq-t)      
  --
  C-UP : 
    {Γ Δ : Con}
    {sΔ : Ctx Δ len'}
    {A : Ty Γ n}
    {s : Tm Γ A}
    {η : Sub · Γ}
    {σ : Stack Δ ms}
    {σ' : Stack Δ ns}
    {A' : Ty Δ n}
    {t' : Tm Δ A'}
    ----
    {B : Ty Δ m}
    {t : Tm Δ B}
    {ins : Is D sΔ d (σ ∷ ↑ t) (σ' ∷ t')}
    {env : Env D len'}
    {st : Env D ms}
    {sf : Sf D s η lf}
    ----
    {δ : Sub · Δ}
    {v : Val D (t [ δ ])}
    {wf-env : env ⊨ sΔ as δ}
    {wf-st : wf-env ⊢ st ⊨ˢ σ}
    {eq-A : A' [ δ ]T b.≡ A [ η ]T}
    {eq-t : s [ η ] b.≡ Tm-subst (t' [ δ ]) (b.cong-app eq-A)} →  
    ----------------------------
    I ⊢ (conf (UP >> ins) env (st ∷ v) sf wf-env (cons wf-st b.refl b.refl) eq-A eq-t) 
      ↝ (conf ins env (st ∷ lift v) sf wf-env (cons wf-st b.refl b.refl) eq-A eq-t)      
  --
  C-DOWN : 
    {Γ Δ : Con}
    {sΔ : Ctx Δ len'}
    {A : Ty Γ n}
    {s : Tm Γ A}
    {η : Sub · Γ}
    {σ : Stack Δ ms}
    {σ' : Stack Δ ns}
    {A' : Ty Δ n}
    {t' : Tm Δ A'}
    ----
    {B : Ty Δ m}
    {t : Tm Δ B}
    {ins : Is D sΔ d (σ ∷ t) (σ' ∷ t')}
    {env : Env D len'}
    {st : Env D ms}
    {sf : Sf D s η lf}
    ----
    {δ : Sub · Δ}
    {v : Val D (t [ δ ])}
    {wf-env : env ⊨ sΔ as δ}
    {wf-st : wf-env ⊢ st ⊨ˢ σ}
    {eq-A : A' [ δ ]T b.≡ A [ η ]T}
    {eq-t : s [ η ] b.≡ Tm-subst (t' [ δ ]) (b.cong-app eq-A)} →  
    ----------------------------
    I ⊢ (conf (DOWN >> ins) env (st ∷ lift v) sf wf-env (cons wf-st b.refl b.refl) eq-A eq-t) 
      ↝ (conf ins env (st ∷ v) sf wf-env (cons wf-st b.refl b.refl) eq-A eq-t)

infixr 20 _⟫_
data _⊢_↝*_ {D : LCon} (I : Impl D) (c : Config D) : Config D → Set₁ where
  ■ : I ⊢ c ↝* c
  _⟫_ : ∀{c' c'' : Config D} → I ⊢ c ↝ c' → I ⊢ c' ↝* c'' → I ⊢ c ↝* c''

data _⊢_⇓_ 
  {D : LCon} {A : Type (b.suc n)} {t : Tm · (λ _ → A)}
  (I : Impl D) (c : Config D) (v : Val D t) : Set₁ where
  --
  Halt : 
    ∀ {σ : Stack · ns} 
      {st : Env D ns} 
      {wf-st : nil ⊢ st ⊨ˢ σ} →
    I ⊢ c ↝* conf (RET {d = d} {σ = σ ∷ t}) ◆ (st ∷ v) (◆ v) nil (cons wf-st b.refl b.refl) b.refl b.refl → 
    -------------------------------------------------------
    I ⊢ c ⇓ v

 