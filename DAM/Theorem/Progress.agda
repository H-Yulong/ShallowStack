module DAM.Theorem.Progress where

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

open b using (ℕ; _+_; _+T_; inL; inR)
open LCon

private variable
  m n m' len len' ms ms' ns ns' lf d d' id : ℕ

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
Progress I {ins = RET} {st = st ∷ v} {sf = ◆ t} {wf-st = cons wf-st b.refl b.refl} = inL (Halt! v (Halt ■))
Progress I {ins = RET} {st = st ∷ v} {sf = sf ∷ _} {wf-st = cons wf-st b.refl b.refl} = inR (_ b., C-RET)
Progress I {ins = NOP >> ins} = inR (_ b., C-NOP)
Progress I {ins = VAR x >> ins} = inR (_ b., C-VAR)
Progress I {ins = POP >> ins} {st = st ∷ v} {wf-st = cons wf-st b.refl b.refl} = inR (_ b., C-POP)
Progress I {ins = APP >> ins} {st = st ∷ clo L env' ⦃ wf-env' ⦄ ∷ v2} {wf-st = cons (cons wf-st ptt₁ eq₁) b.refl b.refl} = 
  inR (_ b., C-APP)
Progress I {ins = CLO ms' L ⦃ pf ⦄ >> ins} {st = st} = inR (_ b., C-CLO)
Progress I {ins = CLOENV L >> ins} = inR (_ b., C-CLOENV)
Progress I {ins = LIT n >> ins} = inR (_ b., C-LIT)
Progress I {ins = TY A >> ins} = inR (_ b., C-TY)
Progress I {ins = SWP >> ins} {st = st ∷ v ∷ v'} {wf-st = cons (cons wf-st b.refl b.refl) b.refl b.refl}= inR (_ b., C-SWP)
Progress I {ins = ST x >> ins} = inR (_ b., C-ST)
Progress I {ins = INC >> ins} {st = st ∷ lit-n n} {wf-st = cons wf-st b.refl eq-x} = inR (_ b., C-INC)
Progress I {ins = ITER P Z S >> ins} {st = st ∷ lit-n ℕ.zero} {wf-st = cons wf-st b.refl eq-x} = inR (_ b., C-ITER-Z)
Progress I {ins = ITER P Z S >> ins} {st = st ∷ lit-n (ℕ.suc n)} {wf-st = cons wf-st b.refl eq-x} = inR (_ b., C-ITER-S)
Progress I {ins = UNIT >> ins} = inR (_ b., C-UNIT)
Progress I {ins = PAIR >> ins} {st = st ∷ v₁ ∷ v₂} {wf-st = cons (cons wf-st b.refl b.refl) b.refl b.refl} = inR (_ b., C-PAIR)
Progress I {ins = FST >> ins} {st = st ∷ pair v₁ v₂} {wf-st = cons wf-st ptt eq} = inR (_ b., C-FST)
Progress I {ins = SND >> ins} {st = st ∷ pair v₁ v₂} {wf-st = cons wf-st ptt eq} = inR (_ b., C-SND)
Progress I {ins = UP >> ins} {st = st ∷ v} {wf-st = cons wf-st b.refl b.refl} = inR (_ b., C-UP)
Progress I {ins = DOWN >> ins} {st = st ∷ lift v} {wf-st = cons wf-st b.refl b.refl} = inR (_ b., C-DOWN) 
