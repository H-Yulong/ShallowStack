module DAM.Examples.Vector.Zip.Code where

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
import DAM.Examples.Vector.Zip.Source as 𝓢


private variable
  Γ : Con
  len i j k l m n id : b.ℕ
  sΓ : Ctx Γ len

data Pi : (id : b.ℕ) (sΓ : Ctx Γ len) (A : Ty Γ n) (B : Ty (Γ ▹ A) n) → Set₁ where 
  -- Zero case 
  Zip-Z0 : Pi 0 (𝓢.sΔ ∷ Vec 𝟚 𝟙 ∷ ⊤ ∷ 𝓢.Az) 𝓢.Bz 𝓢.ABz
  Zip-Z1 : Pi 1 (𝓢.sΔ ∷ Vec 𝟚 𝟙 ∷ ⊤) 𝓢.Az (Π 𝓢.Bz 𝓢.ABz)
  Zip-Z : Pi 2 (𝓢.sΔ ∷ Vec 𝟚 𝟙) ⊤ (𝓢.P [ p ▻ zero ]T)
  -- Suc case
  Zip-S0 : Pi 0 (𝓢.sΔ ∷ Vec 𝟚 𝟙 ∷ Nat ∷ 𝓢.P ∷ 𝓢.As) 𝓢.Bs 𝓢.ABs
  Zip-S1 : Pi 1 (𝓢.sΔ ∷ Vec 𝟚 𝟙 ∷ Nat ∷ 𝓢.P) 𝓢.As (Π 𝓢.Bs 𝓢.ABs)
  Zip-S : Pi 2 (𝓢.sΔ ∷ Vec 𝟚 𝟙 ∷ Nat) 𝓢.P (𝓢.P [ p² ▻ suc 𝟙 ]T)
  -- Zip
  Zip0 : Pi 3 𝓢.sΔ (Vec 𝟚 𝟙) (Vec (c 𝓢.AxB) 𝟚)


interp : ∀{A : Ty Γ n}{B : Ty (Γ ▹ A) n} → Pi id sΓ A B → Tm (Γ ▹ A) B

_⟦_⟧ : ∀{Δ : Con}{A : Ty Γ n}{B : Ty (Γ ▹ A) n} → 
    ----
      (lab : Pi id sΓ A B) → 
      (σ : Sub Δ Γ) → 
    -----------------------------------
    Tm Δ (Π (A [ σ ]T) (B [ σ ^ A ]T))

interp Zip0 = (iter 𝓢.P ((Zip-Z ⟦ ✧ ⟧) $ tt) (Zip-S1 ⟦ ✧ ⟧) 𝟚) $ 𝟙 $ 𝟘
interp Zip-Z0 = tt
interp Zip-Z1 = Zip-Z0 ⟦ ✧ ⟧
interp Zip-Z = Zip-Z1 ⟦ ✧ ⟧
interp Zip-S0 = ((fst 𝟙) , (fst 𝟘)) , (𝟚 $ (snd 𝟙) $ (snd 𝟘))
interp Zip-S1 = Zip-S0 ⟦ ✧ ⟧
interp Zip-S = Zip-S1 ⟦ ✧ ⟧

L ⟦ σ ⟧ = ~λ (λ γ α → (interp L) ~$ (σ γ ~, α))

D : LCon
D = record { Pi = Pi ; interp = interp} 

impl : ∀{A : Ty Γ n}{B : Ty (Γ ▹ A) n}
  (lab : Pi id sΓ A B) → Proc D id (sΓ ∷ A) (interp lab)
impl Zip-Z0 = proc
  (  UNIT
  >> RET)
impl Zip-Z1 = proc
  (  CLOENV Zip-Z0
  >> RET)
impl Zip-Z = proc
  (  CLOENV Zip-Z1
  >> RET)
  -- ((fst 𝟙) , (fst 𝟘)) , (𝟚 $ (snd 𝟙) $ (snd 𝟘))
impl Zip-S0 =  proc   
  (  VAR V₁
  >> FST
  >> VAR V₀
  >> FST
  >> PAIR
  >> VAR V₂
  >> VAR V₁
  >> SND
  >> APP
  >> VAR V₀
  >> SND
  >> APP
  >> PAIR
  >> RET)
impl Zip-S1 = proc
  (  CLOENV Zip-S0
  >> RET)
impl Zip-S = proc
  (  CLOENV Zip-S1
  >> RET)
impl Zip0 = proc
  (  VAR V₂
  >> ITER 𝓢.P Zip-Z Zip-S
  >> VAR V₁
  >> APP
  >> VAR V₀
  >> APP
  >> RET)
