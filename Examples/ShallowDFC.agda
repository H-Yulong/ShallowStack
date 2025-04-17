module Examples.ShallowDFC where

open import Agda.Primitive

import Lib.Basic as b
open import Lib.Order

open import Model.Universe hiding (⟦_⟧)
open import Model.Shallow

import Examples.Compose as Com
import Examples.App as App

open import Model.Labels
open import Model.Context
open import Model.Stack

private variable
  Γ : Con
  len i j k l m n id : b.ℕ
  sΓ : Ctx Γ len

-- private variable
  -- i j k i' j' k' : Level
  -- Γ : Con i
  -- A : Ty Γ j
  -- B : Ty (Γ ▹ A) k
  -- l m n l' m' n' id : lib.ℕ
  -- sΓ : Ctx Γ l

-- open import Theory

-- This definition resolves the three problems with defunctionalization,
-- which are outlined in "Defunctionalization with dependent types":
--
-- 1. Positivity, i.e. the problem of having (Pi A B → Pi A B) → Pi A B,
--    and Pi (Pi A B) C. Solved in the same way as simply-typed DFC, by
--    using some encoding of types as indices, in this case the shallow
--    embedding.
-- 2. Universe levels, i.e. there're always free variables larger than
--    the universe of Pi A B. Solved by using Setω.
-- 3. Termination, i.e. interp Add1 involves interp Add0, but nothing is
--    decreasing. Solved by adding index (n : ℕ), such that a label of
--    (Pi n) can only refer to labels of (Pi m) where m ≤ n, which is a 
--    syntactic constraint in DCC.

-- That said, being theoretically capable of expressing DFC is not enough ─
-- the code should be type-checked in reasonable amount of time.
-- If written naively, Agda's type checker spends exponential time on elaboration,
-- and type-checking definitions like composition just cannot terminate soon.
-- The solution, as shown in Compose.agda, is to build many intermediate values
-- to be re-used by Agda during type-checking.

-- Finally, a trivial point:
-- The label order should be 0,1,2,3... if we're strictly following the DCC scheme:
-- each label gets to refer to all previous labels.
-- Here, the range of labels from disjoint sets,
-- so I can assign individual orders to them.

-- With everything resolved, this file type-checks fast enough.
data Pi : (id : b.ℕ) (sΓ : Ctx Γ len) (A : Ty Γ n) (B : Ty (Γ ▹ A) n) → Set₁ where
  --
  Add0 : Pi 0 (◆ ∷ Nat) Nat Nat
  Add : Pi 1 ◆ Nat (Π Nat Nat)
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
  LNat : Pi 0 ◆ (↑T Nat) U0

mutual
  interp : ∀{A : Ty Γ n}{B : Ty (Γ ▹ A) n} → Pi id sΓ A B → Tm (Γ ▹ A) B
  --
  interp Add0 = iter Nat 𝟘 (suc 𝟘) 𝟙
  interp Add = Add0 ⟦ ✧ ⟧
  -- --
  interp Iden0 = 𝟘
  interp Iden = ↑ (Iden0 ⟦ ✧ ⟧)
  -- -- --
  interp App0 = 𝟙 $ 𝟘
  interp App1 = App0 ⟦ ✧ ⟧
  interp App2 = ↑ (App1 ⟦ ✧ ⟧)
  interp App = App2 ⟦ ✧ ⟧
  -- -- --
  interp Com0 = 𝟚 $ 𝟘 $ (𝟙 $ 𝟘)
  interp Com1 = Com0 ⟦ ✧ ⟧
  interp Com2 = Com1 ⟦ ✧ ⟧
  interp Com3 = ↑ (Com2 ⟦ ✧ ⟧)
  interp Com4 = Com3 ⟦ ✧ ⟧
  interp Com = Com4 ⟦ ✧ ⟧
  -- -- --
  interp LNat = c Nat

  _⟦_⟧ : ∀{Δ : Con}{A : Ty Γ n}{B : Ty (Γ ▹ A) n} → 
    ----
      (lab : Pi id sΓ A B) → 
      (σ : Sub Δ Γ) → 
    -----------------------------------
    Tm Δ (Π (A [ σ ]T) (B [ σ ^ A ]T))
  L ⟦ σ ⟧ = ~λ (λ γ α → (interp L) ~$ (σ γ ~, α))

-- The equational theory is just refl

D : LCon
D = record { Pi = Pi ; interp = interp; lapp = _⟦_⟧; lapp[] = b.refl } 
{-
impl : ∀{A : Ty Γ n}{B : Ty (Γ ▹ A) n}
  (lab : Pi id sΓ A B) → Proc D (sΓ ∷ A) id (interp lab)
impl Add0 = proc 
  (  VAR V₁ 
  >> ITER Nat (VAR V₀ >> RET) (POP >> INC >> RET) 
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
impl LNat = proc 
  (  TLIT Nat
  >> RET )

Lib : Library
Lib = library D impl
-}
 