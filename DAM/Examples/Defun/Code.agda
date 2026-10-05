module DAM.Examples.Defun.Code where

open import Agda.Primitive

import Lib.Basic as b
open import Lib.Order

open import Model.Universe hiding (⟦_⟧)
open import Model.Shallow

import DAM.Examples.Defun.Compose as Com
import DAM.Examples.Defun.App as App

open import DAM.Labels hiding (Pi; interp)
open import Model.Context
open import Model.Stack
open import DAM.Syntax

private variable
  Γ : Con
  len i j k l m n id : b.ℕ
  sΓ : Ctx Γ len

data Pi : (id : b.ℕ) (sΓ : Ctx Γ len) (A : Ty Γ n) (B : Ty (Γ ▹ A) n) → Set₁ where
  --
  Add0-base : ∀{sΓ : Ctx Γ len} → Pi 0 (sΓ ∷ Nat ∷ Nat) ⊤ Nat
  Add0-rec : ∀{sΓ : Ctx Γ len} → Pi 0 (sΓ ∷ Nat ∷ Nat ∷ Nat) Nat Nat
  --
  Add0 : ∀{sΓ : Ctx Γ len} → Pi 1 (sΓ ∷ Nat) Nat Nat
  Add : ∀{sΓ : Ctx Γ len} → Pi 2 sΓ Nat (Π Nat Nat)
  --
  Iden0 : Pi 0 (◆ ∷ U0) (El 𝟘) (El 𝟙)
  Iden : Pi 1 ◆ U0 (↑T (Π (El 𝟘) (El 𝟙)))
  --
  App0 : Pi 0 (◆ ∷ App.A ∷ App.B ∷ App.Tf) (El 𝟚) (El (𝟚 $ ↑ 𝟘))
  App1 : Pi 1 (◆ ∷ App.A ∷ App.B) App.Tf (Π (El 𝟚) (El (𝟚 $ ↑ 𝟘)))
  App2 : Pi 2 (◆ ∷ App.A) App.B (↑T (Π App.Tf (Π (El 𝟚) (El (𝟚 $ ↑ 𝟘)))))
  App : Pi 3  ◆ App.A (Π App.B (↑T (Π App.Tf (Π (El 𝟚) (El (𝟚 $ ↑ 𝟘))))))
  --
  Com0 : Pi 0 (◆ ∷ Com.A ∷ Com.B ∷ Com.C ∷ Com.Tg ∷ Com.Tf) Com.Tx Com.Cxfx
  Com1 : Pi 1 (◆ ∷ Com.A ∷ Com.B ∷ Com.C ∷ Com.Tg) Com.Tf (Π Com.Tx Com.Cxfx)
  Com2 : Pi 2 (◆ ∷ Com.A ∷ Com.B ∷ Com.C) Com.Tg (Π Com.Tf (Π Com.Tx Com.Cxfx))
  Com3 : Pi 3 (◆ ∷ Com.A ∷ Com.B) Com.C (↑T (Π Com.Tg (Π Com.Tf (Π Com.Tx Com.Cxfx))))
  Com4 : Pi 4 (◆ ∷ Com.A) Com.B (Π Com.C (↑T (Π Com.Tg (Π Com.Tf (Π Com.Tx Com.Cxfx)))))
  Com : Pi 5 ◆ Com.A (Π Com.B (Π Com.C (↑T (Π Com.Tg (Π Com.Tf (Π Com.Tx Com.Cxfx))))))
  --
  ConstNat : Pi 0 ◆ (↑T Nat) U0
  --
  IdNat : Pi 0 ◆ Nat Nat

mutual
  interp : ∀{A : Ty Γ n}{B : Ty (Γ ▹ A) n} → Pi id sΓ A B → Tm (Γ ▹ A) B
  interp Add0-base = 𝟙
  interp Add0-rec = suc 𝟘
  --
  interp Add0 = iter Nat 𝟘 (suc 𝟘) 𝟙
  interp (Add {sΓ = sΓ}) = Add0 {sΓ = sΓ} ⟦ ✧ ⟧
  --
  interp Iden0 = 𝟘
  interp Iden = ↑ (Iden0 ⟦ ✧ ⟧)
  --
  interp App0 = 𝟙 $ 𝟘
  interp App1 = App0 ⟦ ✧ ⟧
  interp App2 = ↑ (App1 ⟦ ✧ ⟧)
  interp App = App2 ⟦ ✧ ⟧
  --
  interp Com0 = 𝟚 $ 𝟘 $ (𝟙 $ 𝟘)
  interp Com1 = Com0 ⟦ ✧ ⟧
  interp Com2 = Com1 ⟦ ✧ ⟧
  interp Com3 = ↑ (Com2 ⟦ ✧ ⟧)
  interp Com4 = Com3 ⟦ ✧ ⟧
  interp Com = Com4 ⟦ ✧ ⟧
  --
  interp ConstNat = c Nat
  --
  interp IdNat = 𝟘

  _⟦_⟧ : ∀{Δ : Con}{A : Ty Γ n}{B : Ty (Γ ▹ A) n} → 
    ----
      (lab : Pi id sΓ A B) → 
      (σ : Sub Δ Γ) → 
    -----------------------------------
    Tm Δ (Π (A [ σ ]T) (B [ σ ^ A ]T))
  L ⟦ σ ⟧ = ~λ (λ γ α → (interp L) ~$ (σ γ ~, α))

-- The equational theory is just refl

D : LCon
D = record { Pi = Pi ; interp = interp} 

impl : 
  ∀ {A : Ty Γ n}{B : Ty (Γ ▹ A) n}
    (lab : Pi id sΓ A B) → Proc D id (sΓ ∷ A) (interp lab)
impl Add0-base = proc 
  (  VAR V₁
  >> RET)
impl Add0-rec = proc
  (  VAR V₀
  >> INC 
  >> RET)
impl Add0 = proc 
  (  VAR V₁ 
  >> ITER Nat Add0-base Add0-rec 
  >> RET )
impl Add = proc 
  (  VAR V₀ 
  >> CLO 1 Add0
  >> RET )
impl Iden0 = proc 
  (  VAR V₀
  >> RET )
impl Iden = proc 
  (  VAR V₀ 
  >> CLO 1 Iden0
  >> UP 
  >> RET )
impl App0 = proc 
  (  VAR V₁ 
  >> VAR V₀ 
  >> APP 
  >> RET )
impl App1 = proc 
  (  VAR V₂
  >> VAR V₁
  >> VAR V₀
  >> CLO 3 App0 
  >> RET )
impl App2 = proc 
  (  VAR V₁ 
  >> VAR V₀ 
  >> CLO 2 App1
  >> UP 
  >> RET )
impl App = proc 
  (  VAR V₀ 
  >> CLO 1 App2 
  >> RET )
impl Com0 = proc 
  (  VAR V₂
  >> VAR V₀
  >> APP 
  >> VAR V₁
  >> VAR V₀
  >> APP
  >> APP
  >> RET )
impl Com1 = proc 
  (  VAR (vs V₃)
  >> VAR V₃
  >> VAR V₂
  >> VAR V₁
  >> VAR V₀ 
  >> CLO 5 Com0 
  >> RET )
impl Com2 = proc 
  (  VAR V₃
  >> VAR V₂
  >> VAR V₁
  >> VAR V₀ 
  >> CLO 4 Com1 
  >> RET )
impl Com3 = proc 
  (  VAR V₂
  >> VAR V₁
  >> VAR V₀ 
  >> CLO 3 Com2
  >> UP 
  >> RET )
impl Com4 = proc 
  (  VAR V₁
  >> VAR V₀ 
  >> CLO 2 Com3 
  >> RET )
impl Com = proc
  (  VAR V₀ 
  >> CLO 1 Com4 
  >> RET )
impl ConstNat = proc 
  (  TY Nat
  >> RET )
impl IdNat = proc
  (  VAR V₀
  >> RET)
