{-# OPTIONS --safe #-}

module ShallowDFC where

open import Agda.Primitive
import Basic as lib
open import Shallow

import Compose as Com
import App

-- This definition resolves the three problems with defunctionalization,
-- which are outlined in "Defunctionalization with dependent types":
--
-- 1. Positivity, i.e. the problem of having (Pi A B → Pi A B) → Pi A B,
--    and Pi (Pi A B) C. Solved in the same way as simply-typed DFC, by
--    using some encoding of types as indices, in this case the shallow
--    embedding.
-- 2. Universe levels, i.e. there're always free variables larger than
--    the universe of Pi A B. Solved with Setω.
-- 3. Termination, i.e. interp Add1 involves interp Add0, but nothing is
--    decreasing. Solved by adding index (n : ℕ), such that a label of
--    (Pi n) can only refer to labels of (Pi m) where m ≤ n, which is a 
--    syntactic constraint in DCC.

-- That said, being theoretically capable of expressing DFC is not enough ─
-- the code should be type-checked in reasonable amount of time.
-- If written naively, Agda's type checker spends exponential time on elaboration,
-- and type-checking definitions like composition just cannot to terminate soon.
-- The solution, as shown in Compose.agda, is to build many intermediate values
-- to be re-used by Agda during type-checking.

-- Finally, a trivial point:
-- The label order should be 0,1,2,3... if we're strictly following the DCC scheme:
-- each label gets to refer to all previous labels.
-- Here, the range of labels from disjoint sets,
-- so I can assign individual orders to them.

-- With everything resolved, this file type-checks in less than a second.

data Pi :
  ∀(n : lib.ℕ)
   {i}(Γ : Con i)
   {j}(A : Ty Γ j)
   {k}(B : Ty (Γ ▹ A) k) → Setω where
  ----
  Add0 : Pi 0 (· ▹ Nat) Nat Nat
  Add : Pi 1 · Nat (Π Nat Nat)
  ----
  Iden0 : Pi 0 (· ▹ U0) (El 𝟘) (El 𝟙)
  Iden : Pi 1 · U0 (Π (El 𝟘) (El 𝟙))
  ----
  App0 : Pi 0 App.C0 𝟚 (𝟚 $ 𝟘)
  App1 : Pi 1 App.C1 App.Tf (Π 𝟚 (𝟚 $ 𝟘))
  App2 : Pi 2 App.C2 App.B (Π App.Tf (Π 𝟚 (𝟚 $ 𝟘)))
  App : Pi 3 · App.A (Π App.B (Π App.Tf (Π 𝟚 (𝟚 $ 𝟘))))
  ----
  Com0 : Pi 0 Com.C0 Com.Tx Com.Cxfx
  Com1 : Pi 1 Com.C1 Com.Tf (Π Com.Tx Com.Cxfx)
  Com2 : Pi 2 Com.C2 Com.Tg (Π Com.Tf (Π Com.Tx Com.Cxfx))
  Com3 : Pi 3 Com.C3 Com.C (Π Com.Tg (Π Com.Tf (Π Com.Tx Com.Cxfx)))
  Com4 : Pi 4 Com.C4 Com.B (Π Com.C (Π Com.Tg (Π Com.Tf (Π Com.Tx Com.Cxfx))))
  Com : Pi 5 · Com.A (Π Com.B (Π Com.C (Π Com.Tg (Π Com.Tf (Π Com.Tx Com.Cxfx)))))
  ----
  LNat : Pi 0 · Nat U0

mutual
  interp : 
    ∀{n : lib.ℕ}
     {i}{Γ : Con i}
     {j}{A : Ty Γ j}
     {k}{B : Ty (Γ ▹ A) k} →
     Pi n Γ A B → Tm (Γ ▹ A) B
  ----
  interp Add0 = iter Nat 𝟘 (suc 𝟘) 𝟙
  interp Add = Add0 ⟦ ✧ ⟧
  --
  interp Iden0 = 𝟘
  interp Iden = Iden0 ⟦ ✧ ⟧
  --
  interp App0 = 𝟙 $ 𝟘
  interp App1 = App0 ⟦ ✧ ⟧
  interp App2 = App1 ⟦ ✧ ⟧
  interp App = App2 ⟦ ✧ ⟧
  --
  interp Com0 = 𝟚 $ 𝟘 $ (𝟙 $ 𝟘)
  interp Com1 = Com0 ⟦ ✧ ⟧
  interp Com2 = Com1 ⟦ ✧ ⟧
  interp Com3 = Com2 ⟦ ✧ ⟧
  interp Com4 = Com3 ⟦ ✧ ⟧
  interp Com = Com4 ⟦ ✧ ⟧
  --
  interp LNat = Nat

  _⟦_⟧ : 
    ∀{n : lib.ℕ}
     {i}{Γ : Con i}
     {j}{A : Ty Γ j}
     {k}{B : Ty (Γ ▹ A) k}
     {l}{Δ : Con l} → 
     Pi n Γ A B → (σ : Sub Δ Γ) → 
     Tm Δ (Π (A [ σ ]T) (B [ σ ^ A ]T))
  (L ⟦ σ ⟧) γ α = (interp L) (σ γ lib., α)

-- data SS : Set where
--   instance sss : SS
--   instance ss1 : SS
