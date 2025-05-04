module Examples.Trace where

import Lib.Basic as b
open import Lib.Order

open import Model.Universe hiding (⟦_⟧)
open import Model.Shallow
open import Model.Context
open import Model.Stack

open import Machine.Value
open import Machine.Config
open import Machine.Step

open import Examples.ShallowDFC

{-
module Iden0 where
  prog : Is D ◆ 3 ◆ (◆ ∷ (nat 3))
  prog =
      TLIT Nat
    >> CLO 1 Iden0
    >> LIT 3
    >> APP
    >> RET

  start : Config D
  start = conf prog ◆ ◆ (◆ (lit-n 3)) nil nil b.refl b.refl

  trace : impl ⊢ start ⇓ (lit-n 3)
  trace = Halt (
      C-TLIT
    ⟫ C-CLO
    ⟫ C-LIT
    ⟫ C-APP
    ⟫ C-VAR
    ⟫ ?
    ⟫ ■)
-}

module Identity where

  prog : Is D (◆ ∷ U0 ∷ (El 𝟘)) 3 (◆ ∷ 𝟘) (◆ ∷ 𝟘)
  prog = 
       CLO 0 Iden
    >> VAR V₁
    >> APP
    >> DOWN
    >> SWP
    >> APP
    >> RET

  env : Env D 2
  env = ◆ ∷ ty Nat ∷ lit-n 3

  st : Env D 1
  st = ◆ ∷ lit-n 3

  start : Config D
  start = conf prog env st (◆ (lit-n 3)) 
   (cons (cons nil b.refl) b.refl) 
   (cons nil b.refl b.refl) 
   b.refl b.refl

  -- end : Config D
  -- end = conf 
  --   (RET {sΓ = ◆ ∷ U0 ∷ (El 𝟘)} {d = 3} {σ = ◆ ∷ 𝟘}) 
  --   env (◆ ∷ lit-n 3) ◆ 
  --   (cons (cons nil))
  --   (cons nil b.refl b.refl)
  --   (ε ▻ c Nat ▻ nat 3) 
  --   b.refl

  trace : impl ⊢ start ↝* _
  trace = 
      C-CLO
    ⟫ C-VAR
    ⟫ C-APP
    ⟫ C-VAR
    ⟫ C-CLO
  --   ⟫ C-UP
  --   ⟫ C-RET
  --   ⟫ C-DOWN
  --   ⟫ C-SWP
  --   ⟫ C-APP
  --   ⟫ C-VAR
  --   ⟫ C-RET
    ⟫ ■
 