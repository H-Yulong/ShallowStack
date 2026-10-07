module DAM.Examples.Vector.Append.Code where

open import Agda.Primitive

import Lib.Basic as b
open import Lib.Order

open import Model.Universe hiding (⟦_⟧)
open import Model.Shallow
open import Model.Context
open import Model.Stack

open import DAM.Labels hiding (Pi; interp)
open import DAM.Syntax

open import DAM.Examples.Vector.Vec
import DAM.Examples.Vector.Append.Source as 𝓢


private variable
  Γ : Con
  len i j k l m n id : b.ℕ
  sΓ : Ctx Γ len

data Pi : (id : b.ℕ) (sΓ : Ctx Γ len) (A : Ty Γ n) (B : Ty (Γ ▹ A) n) → Set₁ where 
  -- Nil, cons, hd, tl, in the least curried form
  Nil0 : Pi 0 ◆ U0 (↑T (Vec 𝟘 zero))
  Cons0 : Pi 0 (◆ ∷ U0 ∷ Nat ∷ El 𝟙) (Vec 𝟚 𝟙) (Vec 𝟛 (suc 𝟚))
  Hd0 : Pi 0 (◆ ∷ U0 ∷ Nat) (Vec 𝟙 (suc 𝟘)) (El 𝟚)
  Tl0 : Pi 0 (◆ ∷ U0 ∷ Nat) (Vec 𝟙 (suc 𝟘)) (Vec 𝟚 𝟙)
  -- Append, the zero case
  Append-Z0 : Pi 0 (𝓢.sΔ ∷ Vec 𝟛 𝟙 ∷ ⊤) 𝓢.Az 𝓢.Bz
  Append-Z : Pi 1 (𝓢.sΔ ∷ Vec 𝟛 𝟙) ⊤ (𝓢.P [ p ▻ zero ]T)
  -- Append, the successor case
  Append-S0 : Pi 0 (𝓢.sΔ ∷ Vec 𝟛 𝟙 ∷ Nat ∷ 𝓢.P) 𝓢.As 𝓢.Bs
  Append-S : Pi 1 (𝓢.sΔ ∷ Vec 𝟛 𝟙 ∷ Nat) 𝓢.P (𝓢.P [ p² ▻ suc 𝟙 ]T)
  -- Append
  Append0 : Pi 2 𝓢.sΔ (Vec 𝟛 𝟙) (Vec (𝟛 [ p ]) (add 𝟛 𝟚))

interp : ∀{A : Ty Γ n}{B : Ty (Γ ▹ A) n} → Pi id sΓ A B → Tm (Γ ▹ A) B

_⟦_⟧ : ∀{Δ : Con}{A : Ty Γ n}{B : Ty (Γ ▹ A) n} → 
    ----
      (lab : Pi id sΓ A B) → 
      (σ : Sub Δ Γ) → 
    -----------------------------------
    Tm Δ (Π (A [ σ ]T) (B [ σ ^ A ]T))

interp Nil0 = ↑ tt
interp Cons0 = 𝟙 , 𝟘
interp Hd0 = fst 𝟘
interp Tl0 = snd 𝟘
interp Append0 = (iter 𝓢.P ((Append-Z ⟦ ✧ ⟧) $ tt) (Append-S0 ⟦ ✧ ⟧) 𝟛) $ 𝟙
interp Append-Z = Append-Z0 ⟦ ✧ ⟧
interp Append-Z0 = 𝟚
interp Append-S0 = fst 𝟘 , (𝟙 $ (snd 𝟘))
interp Append-S = Append-S0 ⟦ ✧ ⟧

L ⟦ σ ⟧ = ~λ (λ γ α → (interp L) ~$ (σ γ ~, α))

D : LCon
D = record { Pi = Pi ; interp = interp} 

impl : ∀{A : Ty Γ n}{B : Ty (Γ ▹ A) n}
  (lab : Pi id sΓ A B) → Proc D id (sΓ ∷ A) (interp lab)
impl Nil0 = proc 
  (  UNIT
  >> UP
  >> RET )
impl Cons0 = proc 
  (  VAR V₁
  >> VAR V₀
  >> PAIR
  >> RET )
impl Hd0 = proc 
  (  VAR V₀
  >> FST
  >> RET )
impl Tl0 = proc 
  (  VAR V₀
  >> SND
  >> RET )
impl Append-Z0 = proc 
  (  VAR V₂
  >> RET )
impl Append-Z = proc 
  (  CLOENV Append-Z0
  >> RET )
impl Append-S0 = proc 
  (  VAR V₀
  >> FST
  >> VAR V₁
  >> VAR V₀
  >> SND
  >> APP
  >> PAIR
  >> RET )
impl Append-S = proc 
  (  CLOENV Append-S0
  >> RET )
impl Append0 = proc 
  (  VAR V₃
  >> ITER 𝓢.P Append-Z Append-S
  >> VAR V₁ 
  >> APP
  >> RET )
