module Machine.Theory where

open import Agda.Primitive
import Lib.Basic as b

open import Model.Shallow
open import Model.Context
open import Model.Labels
open import Model.Stack

open import Machine.Value
open import Machine.Config
open import Machine.Step

open b using (ℕ; _+_; _+T_; inL; inR)
open LCon

private variable
  m n m' len len' ms ms' ns ns' lf d d' id : ℕ

{- Process halting -}

data _⊢_⇓-RET {D : LCon} (I : Impl D) : (c : Config D) → Set₁ where
  --
  ◆ : 
    ∀ {Δ : Con}{sΔ : Ctx Δ len}
      {σ : Stack Δ ns}
      {B : Ty Δ m}{t : Tm Δ B}
      {env : Env D len}
      {st : Env D ns}
      --
      {δ : Sub · Δ}
      {wf-env : env ⊨ sΔ as δ}
      {wf-st : wf-env ⊢ st ⊨ˢ σ}
      --
      {Γ : Con}{A' : Ty Γ m}{s : Tm Γ A'}{η : Sub · Γ}
      {sf : Sf D s η lf}
      {v : Val D (t [ δ ])}
      {eq-A : B [ δ ]T b.≡ A' [ η ]T}
      {eq-t : s [ η ] b.≡ Tm-subst (t [ δ ]) (b.cong-app eq-A)} →  
    I ⊢ (conf (RET {σ = σ ∷ t}) env (st ∷ v) sf wf-env (cons wf-st b.refl b.refl) eq-A eq-t) ⇓-RET 
  --
  _⟫_ : ∀{c c' : Config D} → I ⊢ c ↝ c' → I ⊢ c' ⇓-RET → I ⊢ c ⇓-RET

-- Progress
Progress : 
  ∀ {D : LCon}
    (I : Impl D)
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
    {ins : Is D sΔ σ (σ' ∷ t')}
    {env : Env D len'}
    {st : Env D ms}
    {sf : Sf D s η lf}
    ----
    {δ : Sub · Δ}
    {wf-env : env ⊨ sΔ as δ}
    {wf-st : wf-env ⊢ st ⊨ˢ σ}
    {eq-A : A' [ δ ]T b.≡ A [ η ]T}
    {eq-t : s [ η ] b.≡ Tm-subst (t' [ δ ]) (b.cong-app eq-A)} → 
      let c = conf ins env st sf wf-env wf-st eq-A eq-t in
        (I ⊢ c ⇓!) +T (b.Σ (Config D) (λ c' → I ⊢ c ↝ c'))
Progress I {ins = RET} {st = st ∷ v} {sf = ◆ v'} {wf-st = cons wf-st b.refl b.refl} = inL (Halt! v' (Halt ■))
Progress I {ins = RET} {st = st ∷ v} {sf = sf ∷ _} {wf-st = cons wf-st b.refl b.refl} = inR (_ b., C-RET)
Progress I {ins = NOP >> ins} = inR (_ b., C-NOP)
Progress I {ins = VAR x >> ins} = inR (_ b., C-VAR)
Progress I {ins = POP >> ins} {st = st ∷ v} {wf-st = cons wf-st b.refl b.refl} = inR (_ b., C-POP)
-- Progress I {ins = TPOP >> ins} = {!   !}
Progress I {ins = APP >> ins} {st = st ∷ clo L env' ⦃ wf-env' ⦄ ∷ v2} {wf-st = cons (cons wf-st ptt₁ eq₁) b.refl b.refl} = 
  inR (_ b., C-APP)
Progress I {ins = CLO ms' L ⦃ pf ⦄ >> ins} {st = st} = inR (_ b., C-CLO)
Progress I {ins = LIT n >> ins} = inR (_ b., C-LIT)
Progress I {ins = TLIT A >> ins} = inR (_ b., C-TLIT)
Progress I {ins = SWP >> ins} {st = st ∷ v ∷ v'} {wf-st = cons (cons wf-st b.refl b.refl) b.refl b.refl}= inR (_ b., C-SWP)
Progress I {ins = ST x >> ins} = inR (_ b., C-ST)
Progress I {ins = INC >> ins} {st = st ∷ lit-n n} {wf-st = cons wf-st b.refl eq-x} = inR (_ b., C-INC)
Progress I {ins = ITER P Z S >> ins} {st = st ∷ lit-n ℕ.zero} {wf-st = cons wf-st b.refl eq-x} = inR (_ b., C-ITER-Z)
Progress I {ins = ITER P Z S >> ins} {st = st ∷ lit-n (ℕ.suc n)} {wf-st = cons wf-st b.refl eq-x} = inR (_ b., C-ITER-S)
-- Progress I {ins = IF P T F >> ins} = {!   !}
-- Progress I {ins = TRUE >> ins} = {!   !}
-- Progress I {ins = FALSE >> ins} = {!   !}
-- Progress I {ins = UNIT >> ins} = {!   !}
Progress I {ins = PAIR >> ins} {st = st ∷ v₁ ∷ v₂} {wf-st = cons (cons wf-st b.refl b.refl) b.refl b.refl} = inR (_ b., C-PAIR)
Progress I {ins = FST >> ins} {st = st ∷ pair v₁ v₂} {wf-st = cons wf-st ptt eq} = inR (_ b., C-FST)
Progress I {ins = SND >> ins} {st = st ∷ pair v₁ v₂} {wf-st = cons wf-st ptt eq} = inR (_ b., C-SND)
-- Progress I {ins = REFL u >> ins} = {!   !}
-- Progress I {ins = JRULE C pf W > > ins} = {!   !}
Progress I {ins = UP >> ins} {st = st ∷ v} {wf-st = cons wf-st b.refl b.refl} = inR (_ b., C-UP)
Progress I {ins = DOWN >> ins} {st = st ∷ lift v} {wf-st = cons wf-st b.refl b.refl} = inR (_ b., C-DOWN) 

step : ∀{D : LCon} → (I : Impl D) → (c : Config D) → ℕ → (I ⊢ c ⇓!) +T (b.Σ (Config D) (λ c' → I ⊢ c ↝* c'))
step {D} I (conf ins env st sf wf-env wf-st eq-A eq-t) n = aux n
  where
    aux :
      ∀{n}
      (fuel : ℕ) → 
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
      {ins : Is D sΔ σ (σ' ∷ t')}
      {env : Env D len'}
      {st : Env D ms}
      {sf : Sf D s η lf}
      ----
      {δ : Sub · Δ}
      {wf-env : env ⊨ sΔ as δ}
      {wf-st : wf-env ⊢ st ⊨ˢ σ}
      {eq-A : A' [ δ ]T b.≡ A [ η ]T}
      {eq-t : s [ η ] b.≡ Tm-subst (t' [ δ ]) (b.cong-app eq-A)} → 
        let c = conf ins env st sf wf-env wf-st eq-A eq-t in
          (I ⊢ c ⇓!) +T (b.Σ (Config D) (λ c' → I ⊢ c ↝* c'))
    aux ℕ.zero {ins = ins} {env} {st} {sf} {wf-env = wf-env} {wf-st} {eq-A} {eq-t} = inR (_ b., ■)
    aux (ℕ.suc fuel) {ins = ins} {env} {st} {sf} {wf-env = wf-env} {wf-st} {eq-A} {eq-t}
      with Progress I {ins = ins} {env} {st} {sf} {wf-env = wf-env} {wf-st} {eq-A} {eq-t}
    ... | inL h = inL h
    ... | inR (conf ins' env' st' sf' wf-env' wf-st' eq-A' eq-t' b., s)
      with aux fuel {ins = ins'} {env'} {st'} {sf'} {wf-env = wf-env'} {wf-st'} {eq-A'} {eq-t'}
    ... | inL (Halt! v (Halt trace)) = inL (Halt! v (Halt (s ⟫ trace)))
    ... | inR (_ b., trace) = inR (_ b., s ⟫ trace)

-- Exec : ∀{D : LCon} → (I : Impl D) → (c : Config D) → ℕ → b.Bool b.× (b.Σ (Config D) (λ c' → I ⊢ c ↝* c'))
-- Exec I c n with step I c n
-- ... | inL (Halt! v (Halt trace)) = b.true b., (_ b., trace)
-- ... | inR (c b., trace) = b.false b., (c b., trace)

Exec : 
  ∀ {D : LCon}{A : Ty · m}{σ : Stack · ns}{t : Tm · A} → 
    ℕ → (I : Impl D) → (ins : Is D ◆ ◆ (σ ∷ t)) → (v : Val D t) → 
    let c = conf ins ◆ ◆ (◆ v) nil nil b.refl b.refl in
  b.Bool b.× (b.Σ (Config D) (λ c' → I ⊢ c ↝* c'))
Exec n I ins v with step I (conf ins ◆ ◆ (◆ v) nil nil b.refl b.refl) n
... | inL (Halt! v (Halt trace)) = b.true b., (_ b., trace)
... | inR (c b., trace) = b.false b., (c b., trace)
