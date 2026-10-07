module DAM.Syntax where

open import Agda.Primitive
import Lib.Basic as b

open import Lib.Order

open import Model.Universe hiding (⟦_⟧)
open import Model.Shallow
open import Model.Context
open import Model.Stack
open import DAM.Labels

open b using (ℕ; _+_)
open LCon

infixr 20 _>>_

private variable
  m n ms ns len len' id id' : ℕ  
  Γ : Con
  σ : Stack Γ ns

mutual

  data Is (D : LCon)(sΓ : Ctx Γ len) : Stack Γ ms → Stack Γ ns → Set₁ where
    --
    RET : Is D sΓ σ σ
    --
    _>>_ : 
      {σ' : Stack Γ ms}{σ'' : Stack Γ ns} → 
      Instr D sΓ σ σ' → Is D sΓ σ' σ'' → Is D sΓ σ σ''

  data Instr (D : LCon)(sΓ : Ctx Γ len) : Stack Γ ms → Stack Γ ns → Set₁ where
    NOP : Instr D sΓ σ σ
    --
    VAR : {A : Ty Γ n}(x : V sΓ A) → Instr D sΓ σ (σ ∷ ⟦ x ⟧V)
    --
    POP : {A : Ty Γ n}{t : Tm Γ A} → Instr D sΓ (σ ∷ t) σ
    --
    -- TPOP : ∀{A : Tm Γ (U n)} → Instr D sΓ (σ ∷ A) σ
    --
    APP : 
        {A : Ty Γ n}{B : Ty (Γ ▹ A) n}
        {f : Tm Γ (Π A B)} {a : Tm Γ A} → 
      Instr D sΓ (σ ∷ f ∷ a) (σ ∷ f $ a)
    --
    CLO : 
      ∀ (ns : b.ℕ)
        {Δ}{sΔ : Ctx Δ ns}
        {A : Ty Δ n}{B : Ty (Δ ▹ A) n}
        {σ : Stack Γ (ns + ms)} 
        {δ : Sub Γ Δ}
      (L : Pi D id sΔ A B)
        ⦃ pf : sΓ ⊢ (take ns σ) of sΔ as δ ⦄ →
      Instr D sΓ σ (drop ns σ ∷ lapp D L δ)
    --
    CLOENV : 
      ∀ {A : Ty Γ n}{B : Ty (Γ ▹ A) n} 
      (L : Pi D id sΓ A B) → 
      Instr D sΓ σ (σ ∷ lapp D L ✧)
    --
    LIT : (n : b.ℕ) → Instr D sΓ σ (σ ∷ (nat n))
    --
    TY : (A : Ty Γ n) → Instr D sΓ σ (σ ∷ (c A))
    --
    SWP :
        {A : Ty Γ n}{A' : Ty Γ m}
        {t : Tm Γ A}{t' : Tm Γ A'} → 
      Instr D sΓ (σ ∷ t ∷ t') (σ ∷ t' ∷ t)
    --
    ST : {A : Ty Γ n}(x : SVar σ A) → Instr D sΓ σ (σ ∷ find σ x)
    --
    INC : {x : Tm Γ Nat} → Instr D sΓ (σ ∷ x) (σ ∷ suc x)
    --
    ITER : 
      (P : Ty (Γ ▹ Nat) n)
      (Z : Pi D id sΓ (⊤n n) (P [ p ▻ zero ]T))
      (S : Pi D id' (sΓ ∷ Nat) P (P [ p² ▻ (suc 𝟙) ]T)) 
          {x : Tm Γ Nat} → 
      Instr D sΓ (σ ∷ x) (σ ∷ iter P ((interp D Z) [ ✧ ▻ ttn ]) (interp D S) x)
    --
    UNIT : Instr D sΓ σ (σ ∷ tt)
    --
    PAIR : 
        {A : Ty Γ n}{B : Ty (Γ ▹ A) n}
        {a : Tm Γ A}{b : Tm Γ (B [ ✧ ▻ a ]T)} → 
      Instr D sΓ (σ ∷ a ∷ b) (σ ∷ (_,_ {B = B} a b))
    --
    FST : {A : Ty Γ n}{B : Ty (Γ ▹ A) n}{p : Tm Γ (Σ A B)} → 
      Instr D sΓ (σ ∷ p) (σ ∷ fst p) 
    --
    SND : {A : Ty Γ n}{B : Ty (Γ ▹ A) n}{p : Tm Γ (Σ A B)} → 
      Instr D sΓ (σ ∷ p) (σ ∷ snd p) 
    UP : {A : Ty Γ n}{t : Tm Γ A} → 
      Instr D sΓ (σ ∷ t) (σ ∷ ↑ t)
    --
    DOWN : {A : Ty Γ n}{t : Tm Γ A} → 
      Instr D sΓ (σ ∷ ↑ t) (σ ∷ t)

#id : 
  {D : LCon}{sΓ : Ctx Γ len}{σ : Stack Γ ms}{σ' : Stack Γ ns} → 
  Is D sΓ σ σ' → ℕ
#id RET = 0
#id (CLO {id = id} ns L >> ins) = (b.suc id) ⊔n (#id ins)
#id (CLOENV {id = id} L >> ins) = (b.suc id) ⊔n (#id ins)
#id (ITER {id = id} {id' = id'} P Z S >> ins) = (b.suc id) ⊔n (b.suc id') ⊔n #id ins
#id (_ >> ins) = #id ins

record Proc (D : LCon) (id : ℕ) (sΓ : Ctx Γ len) {A : Ty Γ n} (t : Tm Γ A): Set₁ where
  constructor proc
  field
    {nr} : b.ℕ
    {σ'} : Stack Γ nr
    instr : Is D sΓ ◆ (σ' ∷ t)
    ⦃ wf ⦄ : #id instr < (b.suc id) 

Impl : (D : LCon) → Set₁
Impl D = 
  ∀ {id Γ len n}{sΓ : Ctx Γ len}
    {A : Ty Γ n}{B : Ty (Γ ▹ A) n} → 
    (lab : Pi D id sΓ A B) → Proc D id (sΓ ∷ A) (interp D lab)
