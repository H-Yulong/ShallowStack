module SECD.Opsem where

{- Intrinsic operational semantics -}

import Lib.Basic as b
open import Lib.Order

open import Model.Universe
open import Model.Shallow
open import Model.Context
open import Model.Stack

open import SECD.Syntax
open import SECD.Value
open import SECD.Config

open b using (ℕ; _+_)
open Model.Shallow.Lemmas

private variable
  m n m' len len' len'' ms ms' ns ns' nz lf : ℕ

-- The operational semantics is defined only for well-formed configurations,
-- meaning that we have preservation by definition.
data _↝_ : Config → Config → Set₁ where
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
    {ins : Is sΔ σ (σ' ∷ t')}
    {env : Env len'}
    {st : Env ms}
    {sf : Sf s η lf}
    ----
    {δ : Sub · Δ}
    {wf-env : env ⊨ sΔ as δ}
    {wf-st : wf-env ⊢ st ⊨ˢ σ}
    {eq-A : A' [ δ ]T b.≡ A [ η ]T}
    {eq-t : s [ η ] b.≡ Tm-subst (t' [ δ ]) (b.cong-app eq-A)} →
    ----------------------------------------
    (conf (NOP >> ins) env st sf wf-env wf-st eq-A eq-t)
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
    {ins : Is sΔ (σ ∷ ⟦ x ⟧V) (σ' ∷ t')}
    {env : Env len'}
    {st : Env ms}
    {sf : Sf s η lf}
    ----
    {δ : Sub · Δ}
    {wf-env : env ⊨ sΔ as δ}
    {wf-st : wf-env ⊢ st ⊨ˢ σ}
    {eq-A : A' [ δ ]T b.≡ A [ η ]T}
    {eq-t : s [ η ] b.≡ Tm-subst (t' [ δ ]) (b.cong-app eq-A)} →
    ----------------------------
    (conf (VAR x >> ins) env st sf wf-env wf-st eq-A eq-t)
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
    {ins : Is sΔ (σ ∷ find σ x) (σ' ∷ t')}
    {env : Env len'}
    {st : Env ms}
    {sf : Sf s η lf}
    ----
    {δ : Sub · Δ}
    {wf-env : env ⊨ sΔ as δ}
    {wf-st : wf-env ⊢ st ⊨ˢ σ}
    {eq-A : A' [ δ ]T b.≡ A [ η ]T}
    {eq-t : s [ η ] b.≡ Tm-subst (t' [ δ ]) (b.cong-app eq-A)} →
    --------------------------------------
    conf (ST x >> ins) env st sf wf-env wf-st eq-A eq-t
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
    {σ'' : Stack (Δ' ▹ A'') ns'}
    {t'' : Tm (Δ' ▹ A'') B''}
    {ins' : Is (sΔ' ∷ A'') ◆ (σ'' ∷ t'')}
    {ρ : Sub Δ Δ'}
    ----
    {ins : Is sΔ (drop ms' σ ∷ lam t'' [ ρ ]) (σ' ∷ t')}
    {env : Env len'}
    {st : Env (ms' + ms)}
    {sf : Sf s η lf}
    ----
    {δ : Sub · Δ}
    {wf-env : env ⊨ sΔ as δ}
    {wf-st : wf-env ⊢ st ⊨ˢ σ}
    {eq-A : A' [ δ ]T b.≡ A [ η ]T}
    {eq-t : s [ η ] b.≡ Tm-subst (t' [ δ ]) (b.cong-app eq-A)} →
    ----
    ⦃ pf : sΔ ⊢ (take ms' σ) of sΔ' as ρ ⦄ →
    ------------------------------
    let closure = clo (takeᵉ ms' st) ins' ⦃ clo⊨ wf-env (⊨ˢ-take wf-st) pf ⦄ in
    let wf-st' = cons (⊨ˢ-drop wf-st) b.refl b.refl in
    conf (CLO ms' ins' >> ins) env st sf wf-env wf-st eq-A eq-t
      ↝ conf ins env ((dropᵉ ms' st) ∷ closure) sf wf-env wf-st' eq-A eq-t
  --
  C-PUSHC :
    {Γ Δ : Con}
    {sΔ : Ctx Δ len'}
    {A : Ty Γ m}
    {s : Tm Γ A}
    {η : Sub · Γ}
    {σ : Stack Δ ms}
    {σ' : Stack Δ ns}
    {A' : Ty Δ m}
    {t' : Tm Δ A'}
    ----
    {A'' : Ty Δ n}
    {B'' : Ty (Δ ▹ A'') n}
    {σ'' : Stack (Δ ▹ A'') ns'}
    {t'' : Tm (Δ ▹ A'') B''}
    {ins' : Is (sΔ ∷ A'') ◆ (σ'' ∷ t'')}
    ----
    {ins : Is sΔ (σ ∷ lam t'') (σ' ∷ t')}
    {env : Env len'}
    {st : Env ms}
    {sf : Sf s η lf}
    ----
    {δ : Sub · Δ}
    {wf-env : env ⊨ sΔ as δ}
    {wf-st : wf-env ⊢ st ⊨ˢ σ}
    {eq-A : A' [ δ ]T b.≡ A [ η ]T}
    {eq-t : s [ η ] b.≡ Tm-subst (t' [ δ ]) (b.cong-app eq-A)} →
    ------------------------------
    conf (PUSHC ins' >> ins) env st sf wf-env wf-st eq-A eq-t
      ↝ conf ins env (st ∷ clo env ins' ⦃ wf-env ⦄) sf wf-env (cons wf-st b.refl b.refl) eq-A eq-t
  --
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
    {ins : Is sΔ (σ ∷ (f $ a)) (σ' ∷ t')}
    {env : Env len'}
    {st : Env ms}
    {sf : Sf s η lf}
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
    {σ+ : Stack (Δ' ▹ A+) ns'}
    {t+ : Tm (Δ' ▹ A+) B+}
    {ins' : Is (sΔ' ∷ A+) ◆ (σ+ ∷ t+)}
    {env' : Env ms'}
    {wf-env' : env' ⊨ sΔ' as δ'}
    ----
    {pA :  ((Π A+ B+) [ δ' ]T) b.tt b.≡ ((Π A'' B'') [ δ ]T) b.tt}
    {ptf : f [ δ ] b.≡ Tm-subst (lam t+ [ δ' ]) pA}
    {v : Val (a [ δ ])} →
    ------------------------------
    let new-fr = fr ins env st wf-env wf-st eq-A eq-t in
    let eq-A' = b.sym (inj₁ pA) in
    conf (APP {f = f} >> ins) env (st ∷ clo env' ins' ⦃ wf-env' ⦄ ∷ v) sf wf-env (cons (cons wf-st pA ptf) b.refl b.refl) eq-A eq-t
      ↝ conf ins' (env' ∷ v) ◆ (sf ∷ new-fr) (cons wf-env' eq-A') nil
        (b.ext-tt (inj₂ pA (lemma-App1 {A = A''} {δ} {a} (inj₁ pA))))
        (lemma-App2 {f = f} {a = a} pA ptf b.refl)
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
      {ins : Is sΔ' (θ ∷ s) (θ' ∷ s')}
      {env' : Env len'}
      {st' : Env ms'}
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
      {env : Env len}
      {st : Env ms}
      {sf : Sf r η lf}
      ----
      {δ : Sub · Δ}
      {wf-env : env ⊨ sΔ as δ}
      {wf-st : wf-env ⊢ st ⊨ˢ σ}
      {eq-A : A' [ δ ]T b.≡ B [ δ' ]T}
      {eq-t : s [ δ' ] b.≡ Tm-subst (t' [ δ ]) (b.cong-app eq-A)}
      ----
      {v : Val (t' [ δ ])} →
    ------------------------------
    let new-fr = fr ins env' st' wf-env' wf-st' eq-A' eq-t' in
    conf (RET {σ = σ ∷ t'}) env (st ∷ v) (sf ∷ new-fr) wf-env (cons wf-st b.refl b.refl) eq-A eq-t
      ↝ conf ins env' (st' ∷ v) sf wf-env' (cons wf-st' (b.cong-app eq-A) eq-t) eq-A' eq-t'
  --
  C-TY :
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
    {ins : Is sΔ (σ ∷ (c B)) (σ' ∷ t')}
    {env : Env len'}
    {st : Env ms}
    {sf : Sf s η lf}
    ----
    {δ : Sub · Δ}
    {wf-env : env ⊨ sΔ as δ}
    {wf-st : wf-env ⊢ st ⊨ˢ σ}
    {eq-A : A' [ δ ]T b.≡ A [ η ]T}
    {eq-t : s [ η ] b.≡ Tm-subst (t' [ δ ]) (b.cong-app eq-A)} →
    ----------------------------
    (conf (TY B >> ins) env st sf wf-env wf-st eq-A eq-t)
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
    {ins : Is sΔ (σ ∷ (nat k)) (σ' ∷ t')}
    {env : Env len'}
    {st : Env ms}
    {sf : Sf s η lf}
    ----
    {δ : Sub · Δ}
    {wf-env : env ⊨ sΔ as δ}
    {wf-st : wf-env ⊢ st ⊨ˢ σ}
    {eq-A : A' [ δ ]T b.≡ A [ η ]T}
    {eq-t : s [ η ] b.≡ Tm-subst (t' [ δ ]) (b.cong-app eq-A)} →
    ----------------------------
    (conf (LIT k >> ins) env st sf wf-env wf-st eq-A eq-t)
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
    {ins : Is sΔ (σ ∷ t2 ∷ t1) (σ' ∷ t')}
    {env : Env len'}
    {st : Env ms}
    {sf : Sf s η lf}
    ----
    {δ : Sub · Δ}
    {v1 : Val (t1 [ δ ])}
    {v2 : Val (t2 [ δ ])}
    {wf-env : env ⊨ sΔ as δ}
    {wf-st : wf-env ⊢ st ⊨ˢ σ}
    {eq-A : A' [ δ ]T b.≡ A [ η ]T}
    {eq-t : s [ η ] b.≡ Tm-subst (t' [ δ ]) (b.cong-app eq-A)} →
    ----------------------------
    let wf-st1 = cons (cons wf-st b.refl b.refl) b.refl b.refl in
    let wf-st2 = cons (cons wf-st b.refl b.refl) b.refl b.refl in
    (conf (SWP >> ins) env (st ∷ v1 ∷ v2) sf wf-env wf-st1 eq-A eq-t)
      ↝ (conf ins env (st ∷ v2 ∷ v1) sf wf-env wf-st2 eq-A eq-t)
  --
  C-POP :
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
    {ins : Is sΔ σ (σ' ∷ t')}
    {env : Env len'}
    {st : Env ms}
    {sf : Sf s η lf}
    ----
    {δ : Sub · Δ}
    {v : Val (t [ δ ])}
    {wf-env : env ⊨ sΔ as δ}
    {wf-st : wf-env ⊢ st ⊨ˢ σ}
    {eq-A : A' [ δ ]T b.≡ A [ η ]T}
    {eq-t : s [ η ] b.≡ Tm-subst (t' [ δ ]) (b.cong-app eq-A)} →
    ----------------------------
    let wf-st1 = cons wf-st b.refl b.refl in
    (conf ((POP {t = t}) >> ins) env (st ∷ v) sf wf-env wf-st1 eq-A eq-t)
      ↝ (conf ins env st sf wf-env wf-st eq-A eq-t)
  --
  C-INC :
    {Γ Δ : Con}
    {sΔ : Ctx Δ len'}
    {A : Ty Γ n}
    {s : Tm Γ A}
    {η : Sub · Γ}
    {σ : Stack Δ ms}
    {σ' : Stack Δ ns}
    {A' : Ty Δ n}
    {t' : Tm Δ A'}
    {x : Tm Δ Nat}
    ----
    {ins : Is sΔ (σ ∷ (suc x)) (σ' ∷ t')}
    {env : Env len'}
    {st : Env ms}
    {sf : Sf s η lf}
    {n : ℕ}
    ----
    {δ : Sub · Δ}
    {wf-env : env ⊨ sΔ as δ}
    {wf-st : wf-env ⊢ st ⊨ˢ σ}
    {eq-x : x [ δ ] b.≡ nat n}
    {eq-A : A' [ δ ]T b.≡ A [ η ]T}
    {eq-t : s [ η ] b.≡ Tm-subst (t' [ δ ]) (b.cong-app eq-A)} →
    ----------------------------
    conf (INC >> ins) env (st ∷ lit-n n) sf wf-env (cons wf-st b.refl eq-x) eq-A eq-t
      ↝ conf ins env (st ∷ lit-n (b.suc n)) sf wf-env (cons wf-st b.refl (b.cong suc eq-x)) eq-A eq-t
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
    {ins : Is sΔ (σ ∷ ↑ t) (σ' ∷ t')}
    {env : Env len'}
    {st : Env ms}
    {sf : Sf s η lf}
    ----
    {δ : Sub · Δ}
    {v : Val (t [ δ ])}
    {wf-env : env ⊨ sΔ as δ}
    {wf-st : wf-env ⊢ st ⊨ˢ σ}
    {eq-A : A' [ δ ]T b.≡ A [ η ]T}
    {eq-t : s [ η ] b.≡ Tm-subst (t' [ δ ]) (b.cong-app eq-A)} →
    ----------------------------
    (conf (UP >> ins) env (st ∷ v) sf wf-env (cons wf-st b.refl b.refl) eq-A eq-t)
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
    {ins : Is sΔ (σ ∷ t) (σ' ∷ t')}
    {env : Env len'}
    {st : Env ms}
    {sf : Sf s η lf}
    ----
    {δ : Sub · Δ}
    {v : Val (t [ δ ])}
    {wf-env : env ⊨ sΔ as δ}
    {wf-st : wf-env ⊢ st ⊨ˢ σ}
    {eq-A : A' [ δ ]T b.≡ A [ η ]T}
    {eq-t : s [ η ] b.≡ Tm-subst (t' [ δ ]) (b.cong-app eq-A)} →
    ----------------------------
    (conf (DOWN >> ins) env (st ∷ lift v) sf wf-env (cons wf-st b.refl b.refl) eq-A eq-t)
      ↝ (conf ins env (st ∷ v) sf wf-env (cons wf-st b.refl b.refl) eq-A eq-t)
  --
  C-PAIR :
    {Γ Δ : Con}
    {sΔ : Ctx Δ len'}
    {A : Ty Γ n}
    {A' : Ty Δ m}
    {B' : Ty (Δ ▹ A') m}
    {C : Ty Δ n}
    {s : Tm Γ A}
    {η : Sub · Γ}
    {σ : Stack Δ ms}
    {σ' : Stack Δ ns}
    {t₁ : Tm Δ A'}
    {t₂ : Tm Δ (B' [ ✧ ▻ t₁ ]T)}
    {t' : Tm Δ C}
    ----
    {ins : Is sΔ (σ ∷ (_,_ {B = B'} t₁ t₂)) (σ' ∷ t')}
    {env : Env len'}
    {st : Env ms}
    {sf : Sf s η lf}
    ----
    {δ : Sub · Δ}
    {wf-env : env ⊨ sΔ as δ}
    {wf-st : wf-env ⊢ st ⊨ˢ σ}
    {v₁ : Val (t₁ [ δ ])}
    {v₂ : Val (t₂ [ δ ])}
    {eq-A : C [ δ ]T b.≡ A [ η ]T}
    {eq-t : s [ η ] b.≡ Tm-subst (t' [ δ ]) (b.cong-app eq-A)} →
    ----------------------------
    conf (PAIR >> ins) env (st ∷ v₁ ∷ v₂) sf wf-env (cons (cons wf-st b.refl b.refl) b.refl b.refl) eq-A eq-t
      ↝ conf ins env (st ∷ pair {B = B' [ δ ^ A' ]T} v₁ v₂) sf wf-env (cons wf-st b.refl b.refl) eq-A eq-t
  --
  C-FST :
    {Γ Δ : Con}
    {sΔ : Ctx Δ len'}
    {A : Ty Γ n}
    {A' : Ty Δ m}
    {B' : Ty (Δ ▹ A') m}
    {C : Ty Δ n}
    {s : Tm Γ A}
    {η : Sub · Γ}
    {σ : Stack Δ ms}
    {σ' : Stack Δ ns}
    {t : Tm Δ (Σ A' B')}
    {t' : Tm Δ C}
    ----
    {ins : Is sΔ (σ ∷ fst {A = A'} {B = B'} t) (σ' ∷ t')}
    {env : Env len'}
    {st : Env ms}
    {sf : Sf s η lf}
    ----
    {δ : Sub · Δ}
    {wf-env : env ⊨ sΔ as δ}
    {wf-st : wf-env ⊢ st ⊨ˢ σ}
    {eq-A : C [ δ ]T b.≡ A [ η ]T}
    {eq-t : s [ η ] b.≡ Tm-subst (t' [ δ ]) (b.cong-app eq-A)}
    ----
    {A+ : Ty · m}
    {B+ : Ty (· ▹ A+) m}
    {t₁ : Tm · A+}
    {t₂ : Tm · (B+ [ ✧ ▻ t₁ ]T)}
    {v₁ : Val t₁}
    {v₂ : Val t₂}
    {pA :  (Σ A+ B+) b.tt b.≡ ((Σ A' B') [ δ ]T) b.tt}
    {ptf : t [ δ ] b.≡ Tm-subst (_,_ {B = B+} t₁ t₂) pA} →
    ----------------------------
    conf (FST >> ins) env (st ∷ pair v₁ v₂) sf wf-env (cons {t = t} wf-st pA ptf) eq-A eq-t
      ↝ conf ins env (st ∷ v₁) sf wf-env (cons wf-st (Σ-inj₁ pA) (lemma-FST t δ (t₁ , t₂) pA ptf)) eq-A eq-t
  --
  C-SND :
    {Γ Δ : Con}
    {sΔ : Ctx Δ len'}
    {A : Ty Γ n}
    {A' : Ty Δ m}
    {B' : Ty (Δ ▹ A') m}
    {C : Ty Δ n}
    {s : Tm Γ A}
    {η : Sub · Γ}
    {σ : Stack Δ ms}
    {σ' : Stack Δ ns}
    {t : Tm Δ (Σ A' B')}
    {t' : Tm Δ C}
    ----
    {ins : Is sΔ (σ ∷ snd {A = A'} {B = B'} t) (σ' ∷ t')}
    {env : Env len'}
    {st : Env ms}
    {sf : Sf s η lf}
    ----
    {δ : Sub · Δ}
    {wf-env : env ⊨ sΔ as δ}
    {wf-st : wf-env ⊢ st ⊨ˢ σ}
    {eq-A : C [ δ ]T b.≡ A [ η ]T}
    {eq-t : s [ η ] b.≡ Tm-subst (t' [ δ ]) (b.cong-app eq-A)}
    ----
    {A+ : Ty · m}
    {B+ : Ty (· ▹ A+) m}
    {t₁ : Tm · A+}
    {t₂ : Tm · (B+ [ ✧ ▻ t₁ ]T)}
    {v₁ : Val t₁}
    {v₂ : Val t₂}
    {pA :  (Σ A+ B+) b.tt b.≡ ((Σ A' B') [ δ ]T) b.tt}
    {ptf : t [ δ ] b.≡ Tm-subst (_,_ {B = B+} t₁ t₂) pA} →
    ----------------------------
    conf (SND >> ins) env (st ∷ pair v₁ v₂) sf wf-env (cons {t = t} wf-st pA ptf) eq-A eq-t
      ↝ conf ins env (st ∷ v₂) sf wf-env (cons wf-st (Σ-inj₂ pA (lemma-SND1 t δ (t₁ , t₂) pA ptf)) (lemma-SND2 t δ (t₁ , t₂) pA ptf)) eq-A eq-t
  --
  C-UNIT :
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
    {ins : Is sΔ (σ ∷ tt) (σ' ∷ t')}
    {env : Env len'}
    {st : Env ms}
    {sf : Sf s η lf}
    ----
    {δ : Sub · Δ}
    {wf-env : env ⊨ sΔ as δ}
    {wf-st : wf-env ⊢ st ⊨ˢ σ}
    {eq-A : A' [ δ ]T b.≡ A [ η ]T}
    {eq-t : s [ η ] b.≡ Tm-subst (t' [ δ ]) (b.cong-app eq-A)} →
    ----------------------------
    conf (UNIT >> ins) env st sf wf-env wf-st eq-A eq-t
      ↝ conf ins env (st ∷ lit-ttn) sf wf-env (cons wf-st b.refl b.refl) eq-A eq-t
  --
  C-ITER-Z :
    {Γ Δ : Con}
    {sΔ : Ctx Δ len'}
    {A : Ty Γ n}
    {s : Tm Γ A}
    {η : Sub · Γ}
    {σ : Stack Δ ms}
    {σ' : Stack Δ ns}
    {A' : Ty Δ n}
    {t' : Tm Δ A'}
    {x : Tm Δ Nat}
    ----
    {P : Ty (Δ ▹ Nat) m}
    {σz : Stack Δ nz}{z : Tm Δ (P [ ✧ ▻ zero ]T)}
    {Z : Is sΔ ◆ (σz ∷ z)}
    {σs : Stack (Δ ▹ Nat ▹ P) ns'}{s' : Tm (Δ ▹ Nat ▹ P) (P [ p² ▻ (suc 𝟙) ]T)}
    {S : Is (sΔ ∷ Nat ∷ P) ◆ (σs ∷ s')}
    {ins : Is sΔ (σ ∷ iter P z s' x) (σ' ∷ t')}
    {env : Env len'}
    {st : Env ms}
    {sf : Sf s η lf}
    ----
    {δ : Sub · Δ}
    {eq-x : x [ δ ] b.≡ zero}
    {wf-env : env ⊨ sΔ as δ}
    {wf-st : wf-env ⊢ st ⊨ˢ σ}
    {eq-A : A' [ δ ]T b.≡ A [ η ]T}
    {eq-t : s [ η ] b.≡ Tm-subst (t' [ δ ]) (b.cong-app eq-A)} →
    ----------------------------
    conf (ITER P Z S >> ins) env (st ∷ lit-n 0) sf wf-env (cons wf-st b.refl eq-x) eq-A eq-t
      ↝ conf Z env ◆ (sf ∷ fr ins env st wf-env wf-st eq-A eq-t)
        wf-env nil
        (b.cong (λ z → P [ δ ▻ z ]T) (b.sym eq-x))
        (iter-Z (P [ δ ^ Nat ]T) (z [ δ ]) (s' [ δ ^ Nat ^ P ]) (x [ δ ]) eq-x)
  --
  C-ITER-S :
    {Γ Δ : Con}
    {sΔ : Ctx Δ len'}
    {A : Ty Γ n}
    {s : Tm Γ A}
    {η : Sub · Γ}
    {σ : Stack Δ ms}
    {σ' : Stack Δ ns}
    {A' : Ty Δ n}
    {t' : Tm Δ A'}
    {x : Tm Δ Nat}
    ----
    {P : Ty (Δ ▹ Nat) m}
    {σz : Stack Δ nz}{z : Tm Δ (P [ ✧ ▻ zero ]T)}
    {Z : Is sΔ ◆ (σz ∷ z)}
    {σs : Stack (Δ ▹ Nat ▹ P) ns'}{s' : Tm (Δ ▹ Nat ▹ P) (P [ p² ▻ (suc 𝟙) ]T)}
    {S : Is (sΔ ∷ Nat ∷ P) ◆ (σs ∷ s')}
    {ins : Is sΔ (σ ∷ iter P z s' x) (σ' ∷ t')}
    {env : Env len'}
    {y : ℕ}
    {st : Env ms}
    {sf : Sf s η lf}
    ----
    {δ : Sub · Δ}
    {eq-x : x [ δ ] b.≡ nat (b.suc y)}
    {wf-env : env ⊨ sΔ as δ}
    {wf-st : wf-env ⊢ st ⊨ˢ σ}
    {eq-A : A' [ δ ]T b.≡ A [ η ]T}
    {eq-t : s [ η ] b.≡ Tm-subst (t' [ δ ]) (b.cong-app eq-A)} →
    ----------------------------
    conf (ITER P Z S >> ins) env (st ∷ lit-n (b.suc y)) sf wf-env (cons wf-st b.refl eq-x) eq-A eq-t
      ↝ conf (ITER P Z S >> APP {f = lam s' [ ✧ ▻ nat y ]} >> RET) env
          (◆ ∷ clo (env ∷ lit-n y) S ⦃ cons wf-env b.refl ⦄ ∷ lit-n y)
          (sf ∷ fr ins env st wf-env wf-st eq-A eq-t)
          wf-env
          (cons (cons nil b.refl b.refl) b.refl b.refl)
          (b.cong (λ z → P [ δ ▻ z ]T) (b.sym eq-x))
          (iter-S (P [ δ ^ Nat ]T) (z [ δ ]) (s' [ δ ^ Nat ^ P ]) (x [ δ ]) (nat y) eq-x)


infixr 20 _⟫_
data _↝*_ (c : Config) : Config → Set₁ where
  ■ : c ↝* c
  _⟫_ : ∀{c' c'' : Config} → c ↝ c' → c' ↝* c'' → c ↝* c''

data _⇓_ (c : Config) :
  {A : Type (b.suc n)} {t : Tm · (λ _ → A)} (v : Val t) → Set₁ where
    Halt :
      ∀ {Δ : Con}
        {sΔ : Ctx Δ ms}
        {A : Type (b.suc n)}
        {t : Tm · (λ _ → A)}
        {A' : Ty Δ n}
        {t' : Tm Δ A'}
        {σ : Stack Δ ns}
        {δ : Sub · Δ}
        {env : Env ms}
        {st : Env ns}
        {v : Val (t' [ δ ])}
        {wf-env : env ⊨ sΔ as δ}
        {wf-st : wf-env ⊢ st ⊨ˢ σ} →
        {eq-A : A' [ δ ]T b.≡ (λ _ → A)}
        {eq-t : t b.≡ Tm-subst (t' [ δ ]) (b.cong-app eq-A)} →
      c ↝* conf (RET {σ = σ ∷ t'}) env (st ∷ v) (◆ t) wf-env (cons wf-st b.refl b.refl) eq-A eq-t →
      --------------------------------------------------------
      c ⇓ v

data _⇓! (c : Config) : Set₁ where
  --
  Halt! :
    ∀ {A : Type (b.suc n)}
      {t : Tm · (λ _ → A)}
      (v : Val t) → c ⇓ v → c ⇓!
