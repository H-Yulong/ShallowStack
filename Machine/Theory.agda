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

open b using (ℕ; _+_)
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
    I ⊢ (conf (RET {d = d} {σ = σ ∷ t}) env (st ∷ v) sf wf-env (cons wf-st b.refl b.refl) eq-A eq-t) ⇓-RET 
  --
  _⟫_ : ∀{c c' : Config D} → I ⊢ c ↝ c' → I ⊢ c' ⇓-RET → I ⊢ c ⇓-RET

{-
P-Halt :
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
  --------------------------------------
  I ⊢ (conf ins env st sf wf-env wf-st eq-A eq-t) ⇓-RET
P-Halt I {ins = RET} {st = st ∷ v} {wf-st = cons wf-st b.refl b.refl} = ◆
P-Halt I {ins = NOP >> ins} = C-NOP ⟫ (P-Halt I)
P-Halt I {ins = VAR x >> ins} = C-VAR ⟫ (P-Halt I)
P-Halt I {ins = CLO ms' L ⦃ pf ⦄ ⦃ bound ⦄ >> ins} {st = st} = C-CLO ⟫ (P-Halt I)
P-Halt I {ins = LIT n >> ins} = C-LIT ⟫ (P-Halt I)
P-Halt I {ins = TLIT A >> ins} = C-TLIT ⟫ (P-Halt I)
P-Halt I {ins = SWP >> ins} {st = st ∷ t1 ∷ t2} {wf-st = cons (cons wf-st b.refl b.refl) b.refl b.refl} = C-SWP ⟫ (P-Halt I)
P-Halt I {ins = ST x >> ins} = C-ST ⟫ (P-Halt I)
P-Halt I {ins = UP >> ins} {st = st ∷ v} {wf-st = cons wf-st b.refl b.refl} = C-UP ⟫ (P-Halt I)
P-Halt I {ins = DOWN >> ins} {st = st ∷ lift v} {wf-st = cons wf-st b.refl b.refl} = C-DOWN ⟫ (P-Halt I)
P-Halt I {σ = σ ∷ f ∷ a} 
  {ins = APP >> ins} 
  {st = st ∷ clo L env' ⦃ wf-env' ⦄ ∷ v2} 
  {wf-st = cons (cons wf-st ptt₁ eq₁) b.refl b.refl} 
  {eq-A} {eq-t} = C-APP ⟫ {! P-Halt  !}
-}
 
 
   