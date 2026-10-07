module SECD.Syntax where

open import Agda.Primitive
import Lib.Basic as b

open import Lib.Order

open import Model.Universe hiding (⟦_⟧)
open import Model.Shallow
open import Model.Context
open import Model.Stack

open b using (ℕ; _+_)

infixr 20 _>>_

private variable
  m n ms ns ns' nz len : ℕ
  Γ : Con

private variable
  σ : Stack Γ ns

mutual

  data Is (sΓ : Ctx Γ len) : Stack Γ ms → Stack Γ ns → Set₁ where
    --
    RET : Is sΓ σ σ
    --
    _>>_ :
      {σ' : Stack Γ ms}{σ'' : Stack Γ ns} →
      Instr sΓ σ σ' → Is sΓ σ' σ'' → Is sΓ σ σ''

  data Instr (sΓ : Ctx Γ len) : Stack Γ ms → Stack Γ ns → Set₁ where
    NOP : Instr sΓ σ σ
    --
    VAR : {A : Ty Γ n}(x : V sΓ A) → Instr sΓ σ (σ ∷ ⟦ x ⟧V)
    --
    POP : {A : Ty Γ n}{t : Tm Γ A} → Instr sΓ (σ ∷ t) σ
    --
    APP :
        {A : Ty Γ n}{B : Ty (Γ ▹ A) n}
        {f : Tm Γ (Π A B)} {a : Tm Γ A} →
      Instr sΓ (σ ∷ f ∷ a) (σ ∷ f $ a)
    --
    CLO :
      ∀ (ns : ℕ)
        {Δ}{sΔ : Ctx Δ ns}
        {A : Ty Δ n}{B : Ty (Δ ▹ A) n}
        {σ : Stack Γ (ns + ms)}
        {δ : Sub Γ Δ}
        {σ' : Stack (Δ ▹ A) ns'}{t : Tm (Δ ▹ A) B}
      (ins : Is (sΔ ∷ A) ◆ (σ' ∷ t))
        ⦃ pf : sΓ ⊢ (take ns σ) of sΔ as δ ⦄ →
      Instr sΓ σ (drop ns σ ∷ lam t [ δ ])
    --
    PUSHC :
      ∀ {A : Ty Γ n}{B : Ty (Γ ▹ A) n}
        {σ' : Stack (Γ ▹ A) ns'}{t : Tm (Γ ▹ A) B}
      (ins : Is (sΓ ∷ A) ◆ (σ' ∷ t)) →
      Instr sΓ σ (σ ∷ lam t)
    --
    LIT : (n : ℕ) → Instr sΓ σ (σ ∷ (nat n))
    --
    TY : (A : Ty Γ n) → Instr sΓ σ (σ ∷ (c A))
    --
    SWP :
        {A : Ty Γ n}{A' : Ty Γ m}
        {t : Tm Γ A}{t' : Tm Γ A'} →
      Instr sΓ (σ ∷ t ∷ t') (σ ∷ t' ∷ t)
    --
    ST : {A : Ty Γ n}(x : SVar σ A) → Instr sΓ σ (σ ∷ find σ x)
    --
    INC : {x : Tm Γ Nat} → Instr sΓ (σ ∷ x) (σ ∷ suc x)
    --
    ITER :
      (P : Ty (Γ ▹ Nat) n)
        {σz : Stack Γ nz}{z : Tm Γ (P [ ✧ ▻ zero ]T)}
      (Z : Is sΓ ◆ (σz ∷ z))
        {σs : Stack (Γ ▹ Nat ▹ P) ns'}{s : Tm (Γ ▹ Nat ▹ P) (P [ p² ▻ (suc 𝟙) ]T)}
      (S : Is (sΓ ∷ Nat ∷ P) ◆ (σs ∷ s))
        {x : Tm Γ Nat} →
      Instr sΓ (σ ∷ x) (σ ∷ iter P z s x)
    --
    UNIT : Instr sΓ σ (σ ∷ tt)
    --
    PAIR :
        {A : Ty Γ n}{B : Ty (Γ ▹ A) n}
        {a : Tm Γ A}{b : Tm Γ (B [ ✧ ▻ a ]T)} →
      Instr sΓ (σ ∷ a ∷ b) (σ ∷ (_,_ {B = B} a b))
    --
    FST : {A : Ty Γ n}{B : Ty (Γ ▹ A) n}{p : Tm Γ (Σ A B)} →
      Instr sΓ (σ ∷ p) (σ ∷ fst p)
    --
    SND : {A : Ty Γ n}{B : Ty (Γ ▹ A) n}{p : Tm Γ (Σ A B)} →
      Instr sΓ (σ ∷ p) (σ ∷ snd p)
    --
    UP : {A : Ty Γ n}{t : Tm Γ A} →
      Instr sΓ (σ ∷ t) (σ ∷ ↑ t)
    --
    DOWN : {A : Ty Γ n}{t : Tm Γ A} →
      Instr sΓ (σ ∷ ↑ t) (σ ∷ t)
