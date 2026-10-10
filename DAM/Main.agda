module DAM.Main where

import Lib.Basic as b
open import Lib.Order
open b using (ℕ)

open import Model.Universe
open import Model.Shallow hiding (↓; ↓!)
open import Model.Context
open import Model.Stack

open import DAM.Labels
open import DAM.Syntax
open import DAM.Value
open import DAM.Config
open import DAM.Opsem

open import DAM.Theorem.Progress
open import DAM.Theorem.Halting
open import DAM.Theorem.Fundamental
open import DAM.Theorem.Termination

import DAM.Examples.Defun.App
import DAM.Examples.Defun.Compose
import DAM.Examples.Defun.Code

import DAM.Examples.Vector.Vec
import DAM.Examples.Vector.Append.Source
import DAM.Examples.Vector.Append.Code
import DAM.Examples.Vector.Zip.Source
-- Commented out because it takes forever to type-check
-- import DAM.Examples.Vector.Zip.Code

private variable
  m ns : ℕ

module Interpreter {D : LCon} (I : Impl D) where

  all-halt : ∀ (c : Config D) → I ⊢ c ⇓!
  all-halt = Termination I

  Exec :
    ∀ {A : Ty · m}{σ : Stack · ns}{t : Tm · A} →
      (ins : Is D ◆ ◆ (σ ∷ t)) →
      Val D t
  Exec ins = b.fst (TotalCorrectness-program I ins)

  Exec-trace :   
    ∀ {A : Ty · m}{σ : Stack · ns}{t : Tm · A} → 
      (ins : Is D ◆ ◆ (σ ∷ t)) →
      b.Σ (Val D t) (λ v → I ⊢ conf ins ◆ ◆ (◆ t) nil nil b.refl b.refl ⇓ v)
  Exec-trace ins = TotalCorrectness-program I ins

module Add23 where

  open import DAM.Examples.Defun.Code
  open Interpreter impl

  add23 : Is D ◆ ◆ (◆ ∷ nat 5)
  add23 =
      TY Nat
    >> CLO 0 ConstNat
    >> LIT 2
    >> CLO 1 Add0
    >> CLO 3 App0
    >> LIT 3
    >> APP
    >> RET

  run : Val D (nat 5)
  run = Exec add23

  run-trace : b.Σ (Val D (nat 5)) (λ v → impl ⊢ conf add23 ◆ ◆ (◆ (nat 5)) nil nil b.refl b.refl ⇓ v)
  run-trace = Exec-trace add23
