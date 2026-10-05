module SECD.Main where

import Lib.Basic as b
open import Lib.Order
open b using (ℕ)

open import Model.Universe
open import Model.Shallow hiding (↓; ↓!)
open import Model.Context
open import Model.Stack

open import SECD.Syntax
open import SECD.Value
open import SECD.Config
open import SECD.Opsem

open import SECD.Theorem.Progress
open import SECD.Theorem.Halting
open import SECD.Theorem.Fundamental
open import SECD.Theorem.Termination

private variable
  m ns : ℕ

-- Since our proof is constructive, the total correctness theorem
-- also produces an interpreter for the machine.
Exec :
  ∀ {A : Ty · m}{σ : Stack · ns}{t : Tm · A} →
    (ins : Is ◆ ◆ (σ ∷ t)) →
    Val t
Exec ins = b.fst (TotalCorrectness-program ins)

Exec-trace :   
  ∀ {A : Ty · m}{σ : Stack · ns}{t : Tm · A} → 
    (ins : Is ◆ ◆ (σ ∷ t)) →
    b.Σ (Val t) (λ v → conf ins ◆ ◆ (◆ t) nil nil b.refl b.refl ⇓ v)
Exec-trace ins = TotalCorrectness-program ins
