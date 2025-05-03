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
  m n len len' ms ms' ns ns' lf d d' id : ℕ

-- lem : 
--   ∀ {Δ : Con}{A : Ty Γ n}{t : Tm Γ A}
--     {σ ρ : Sub Δ Γ} →
--     (pf : ρ b.≡ σ) →
--   t [ σ ] b.≡ Tm-subst (t [ ρ ]) (b.cong A (b.cong-app pf))
-- lem b.refl = b.refl

-- TODO: too many implicit variables!
-- Refactor to hide things under some abstraction!

-- This intrinsic definition means we have preservation   
data _⊢_↝_ {D : LCon} (I : Impl D) : Config D → Config D → Set₁ where
  C-NOP : 
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
    {sΓ : Ctx Γ len}
    {sΔ : Ctx Δ len'}
    {A : Ty Γ n}
    {s : Tm Γ A}
    {η : Sub · Γ}
    {σ : Stack Δ (ms' + ms)}
    {σ' : Stack Δ ns}
    {A' : Ty Δ n}
    {t' : Tm Δ A'}
    ----
    {Δ' : Con}
    {sΔ' : Ctx Δ' ms'}
    {δ' : Sub · Δ'}
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
    {v : Val D (a [ δ ])}
    → 
    ------------------------------
    let new-fr = fr ins env st wf-env wf-st eq-A eq-t in
    let eq-A' = inj₁ (b.cong-app (b.sym pA)) in
    I ⊢ conf (APP {f = f} >> ins) env (st ∷ clo L env' ⦃ pf ⦄ ∷ v) sf wf-env (cons (cons wf-st (b.cong-app pA) ptf) b.refl b.refl) eq-A eq-t 
      ↝ conf (Proc.instr (I L)) (env' ∷ v) ◆ (sf ∷ new-fr) (cons wf-env' eq-A') nil {!   !} {!   !}

  {--
  --
  C-RET : 
    -- callee env
    {Γ : Con}
    {sΓ : Ctx Γ len}
    {env : Env D len}
    {η : Sub · Γ}
    {wf-env : env ⊨ sΓ as η}
    -- callee stack
    {σ'' : Stack Γ ns'}
    {st : Env D ns'}
    {wf-st : wf-env ⊢ st ⊨ˢ σ''}
    -- return value
    {A : Ty Γ n}
    {t : Tm Γ A}
    {v : Val D (t [ η ])}
    -- previous frames
    {Ω : Con}
    {ω : Sub · Ω}
    {sf : Sf D ω lf}
    -- top frame
    {Δ : Con}
    {sΔ : Ctx Δ len'}
    {δ : Sub · Δ}    
    {ρ : Sub Δ Γ}
    {eqc : η b.≡ ρ ∘ δ}
    {σ : Stack Δ ms}
    {σ' : Stack Δ ns}
    {ins' : Is D sΔ d' (σ ∷ (t [ ρ ])) σ'}
    {env' : Env D len'}
    {st'  : Env D ms}
    {wf-env' : env' ⊨ sΔ as δ}
    {wf-st' : wf-env' ⊢ st' ⊨ˢ σ}
    {ρ' : Sub Ω Δ}
    {eqc' : δ b.≡ ρ' ∘ ω}
    → 
    let frame = fr ins' env' st' wf-env' wf-st' ρ' eqc' in
    I ⊢ conf (RET {d = d} {σ = σ'' ∷ t}) env (st ∷ v) (sf ∷ frame) wf-env (cons {t = t} wf-st b.refl b.refl) ρ eqc
      ↝ conf ins' env' (st' ∷ v) sf wf-env' (cons wf-st' (b.cong A (b.cong-app eqc)) (lem {t = t} eqc)) ρ' eqc'
  --
  C-TLIT : 
    {Δ : Con}
    {δ : Sub · Δ}
    {A : Ty Γ n}
    {σ : Stack Γ ms}
    {σ' : Stack Γ ns}
    {ins : Is D sΓ d (σ ∷ (c A)) σ'}
    {env : Env D len}
    {st : Env D ms}
    {η : Sub · Γ}
    {sf : Sf D δ lf}
    {wf-env : env ⊨ sΓ as η}
    {wf-st : wf-env ⊢ st ⊨ˢ σ}
    {ρ : Sub Δ Γ}
    {eqc : η b.≡ ρ ∘ δ} → 
    ----------------------------
    I ⊢ (conf (TLIT A >> ins) env st sf wf-env wf-st ρ eqc) 
    ↝ (conf ins env (st ∷ ty (A [ η ]T)) sf wf-env (cons wf-st b.refl b.refl) ρ eqc)   
  -- 
  C-LIT : 
    {Δ : Con}
    {δ : Sub · Δ}
    {k : ℕ}
    {σ : Stack Γ ms}
    {σ' : Stack Γ ns}
    {ins : Is D sΓ d (σ ∷ (nat k)) σ'}
    {env : Env D len}
    {st : Env D ms}
    {η : Sub · Γ}
    {sf : Sf D δ lf}
    {wf-env : env ⊨ sΓ as η}
    {wf-st : wf-env ⊢ st ⊨ˢ σ}
    {ρ : Sub Δ Γ}
    {eqc : η b.≡ ρ ∘ δ} → 
    ----------------------------
    I ⊢ (conf (LIT k >> ins) env st sf wf-env wf-st ρ eqc) 
      ↝ (conf ins env (st ∷ lit-n k) sf wf-env (cons wf-st b.refl b.refl) ρ eqc)      
  --
  C-SWP : 
    {Δ : Con}
    {δ : Sub · Δ}
    {A : Ty Γ n}{t : Tm Γ A}
    {B : Ty Γ m}{t' : Tm Γ B}
    {σ : Stack Γ ms}
    {σ' : Stack Γ ns}
    {ins : Is D sΓ d (σ ∷ t' ∷ t) σ'}
    {env : Env D len}
    {st : Env D ms}
    {η : Sub · Γ}
    {sf : Sf D δ lf}
    {wf-env : env ⊨ sΓ as η}
    {wf-st : wf-env ⊢ st ⊨ˢ σ}
    {v : Val D (t [ η ])}
    {v' : Val D (t' [ η ])}
    {ρ : Sub Δ Γ}
    {eqc : η b.≡ ρ ∘ δ} → 
    ----------------------------
    let wf-st1 = cons (cons wf-st b.refl b.refl) b.refl b.refl in
    let wf-st2 = cons (cons wf-st b.refl b.refl) b.refl b.refl in 
    I ⊢ (conf (SWP >> ins) env (st ∷ v ∷ v') sf wf-env wf-st1 ρ eqc) 
      ↝ (conf ins env (st ∷ v' ∷ v) sf wf-env wf-st2 ρ eqc)      
  --
  C-UP : 
    {Δ : Con}
    {δ : Sub · Δ}
    {A : Ty Γ n}
    {t : Tm Γ A}
    {σ : Stack Γ ms}
    {σ' : Stack Γ ns}
    {ins : Is D sΓ d (σ ∷ (↑ t)) σ'}
    {env : Env D len}
    {st : Env D ms}
    {η : Sub · Γ}
    {sf : Sf D δ lf}
    {wf-env : env ⊨ sΓ as η}
    {wf-st : wf-env ⊢ st ⊨ˢ σ}
    {v : Val D (t [ η ])}
    {ρ : Sub Δ Γ}
    {eqc : η b.≡ ρ ∘ δ} → 
    ----------------------------
    I ⊢ (conf (UP >> ins) env (st ∷ v) sf wf-env (cons wf-st b.refl b.refl) ρ eqc) 
      ↝ (conf ins env (st ∷ lift v) sf wf-env (cons wf-st b.refl b.refl) ρ eqc)      
  --
  C-DOWN : 
    {Δ : Con}
    {δ : Sub · Δ}
    {A : Ty Γ n}
    {t : Tm Γ A}
    {σ : Stack Γ ms}
    {σ' : Stack Γ ns}
    {ins : Is D sΓ d (σ ∷ t) σ'}
    {env : Env D len}
    {st : Env D ms}
    {η : Sub · Γ}
    {sf : Sf D δ lf}
    {wf-env : env ⊨ sΓ as η}
    {wf-st : wf-env ⊢ st ⊨ˢ σ}
    {v : Val D (t [ η ])}
    {ρ : Sub Δ Γ}
    {eqc : η b.≡ ρ ∘ δ} → 
    ----------------------------
    I ⊢ (conf (DOWN >> ins) env (st ∷ lift v) sf wf-env (cons wf-st b.refl b.refl) ρ eqc) 
      ↝ (conf ins env (st ∷ v) sf wf-env (cons wf-st b.refl b.refl) ρ eqc)


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
    I ⊢ c ↝* conf (RET {d = d} {σ = σ ∷ t}) ◆ (st ∷ v) ◆ nil (cons wf-st b.refl b.refl) ε b.refl → 
    -------------------------------------------------------
    I ⊢ c ⇓ v
-}
