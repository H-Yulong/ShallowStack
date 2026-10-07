module SECD.Theorem.Progress where

open import Agda.Primitive
import Lib.Basic as b

open import Model.Shallow
open import Model.Context
open import Model.Stack

open import SECD.Syntax
open import SECD.Value
open import SECD.Config
open import SECD.Opsem

open b using (ℕ; _+_; _+T_; inL; inR)

private variable
  m n m' len len' ms ms' ns ns' lf : ℕ

-- Progress
Progress :
  ∀ {Γ Δ : Con}
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
      let c = conf ins env st sf wf-env wf-st eq-A eq-t in
        (c ⇓!) +T (b.Σ Config (λ c' → c ↝ c'))
Progress {ins = RET} {st = st ∷ v} {sf = ◆ t} {wf-st = cons wf-st b.refl b.refl} = inL (Halt! v (Halt ■))
Progress {ins = RET} {st = st ∷ v} {sf = sf ∷ _} {wf-st = cons wf-st b.refl b.refl} = inR (_ b., C-RET)
Progress {ins = NOP >> ins} = inR (_ b., C-NOP)
Progress {ins = VAR x >> ins} = inR (_ b., C-VAR)
Progress {ins = POP >> ins} {st = st ∷ v} {wf-st = cons wf-st b.refl b.refl} = inR (_ b., C-POP)
Progress {ins = APP >> ins} {st = st ∷ clo env' ins' ⦃ wf-env' ⦄ ∷ v2} {wf-st = cons (cons wf-st ptt₁ eq₁) b.refl b.refl} =
  inR (_ b., C-APP)
Progress {ins = CLO ms' ins' ⦃ pf ⦄ >> ins} {st = st} = inR (_ b., C-CLO)
Progress {ins = PUSHC ins' >> ins} = inR (_ b., C-PUSHC)
Progress {ins = LIT n >> ins} = inR (_ b., C-LIT)
Progress {ins = TY A >> ins} = inR (_ b., C-TY)
Progress {ins = SWP >> ins} {st = st ∷ v ∷ v'} {wf-st = cons (cons wf-st b.refl b.refl) b.refl b.refl} = inR (_ b., C-SWP)
Progress {ins = ST x >> ins} = inR (_ b., C-ST)
Progress {ins = INC >> ins} {st = st ∷ lit-n n} {wf-st = cons wf-st b.refl eq-x} = inR (_ b., C-INC)
Progress {ins = ITER P Z S >> ins} {st = st ∷ lit-n ℕ.zero} {wf-st = cons wf-st b.refl eq-x} = inR (_ b., C-ITER-Z)
Progress {ins = ITER P Z S >> ins} {st = st ∷ lit-n (ℕ.suc n)} {wf-st = cons wf-st b.refl eq-x} = inR (_ b., C-ITER-S)
Progress {ins = UNIT >> ins} = inR (_ b., C-UNIT)
Progress {ins = PAIR >> ins} {st = st ∷ v₁ ∷ v₂} {wf-st = cons (cons wf-st b.refl b.refl) b.refl b.refl} = inR (_ b., C-PAIR)
Progress {ins = FST >> ins} {st = st ∷ pair v₁ v₂} {wf-st = cons wf-st ptt eq} = inR (_ b., C-FST)
Progress {ins = SND >> ins} {st = st ∷ pair v₁ v₂} {wf-st = cons wf-st ptt eq} = inR (_ b., C-SND)
Progress {ins = UP >> ins} {st = st ∷ v} {wf-st = cons wf-st b.refl b.refl} = inR (_ b., C-UP)
Progress {ins = DOWN >> ins} {st = st ∷ lift v} {wf-st = cons wf-st b.refl b.refl} = inR (_ b., C-DOWN)
