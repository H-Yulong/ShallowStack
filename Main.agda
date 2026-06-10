module Main where

open import Agda.Primitive

{- Lib -}
import Lib.Basic as b
open import Lib.Order

{- Model: shallow-embedded syntax -}
open import Model.Universe hiding (⟦_⟧)
open import Model.Shallow
open import Model.Context

-- Defunctionalized label contexts
open import Model.Labels

-- Stack machine 
open import Model.Stack

{- Examples -}
import Examples.App
import Examples.Compose
import Examples.Performance
import Examples.ShallowDFC

{- Machine: runtime model and type safety -}
-- Runtime model and type safety
import Machine.Value
import Machine.Config
import Machine.Step
import Machine.Theory

-- Examples of the source language,
-- shallow-embedded Martin-Löf type theory

module SourceExamples where
  
  -- Identity
  test1 : Tm · (Π U0 (Π (↑T (El 𝟘)) (↑T (El 𝟙))))
  test1 = lam (lam 𝟘)

  -- (A : Set) → A → A
  -- λ A : Set. λ x : A . x

  -- Application
  -- It takes a while to check this
  -- Might take even longer to check full dependent composition
  -- test2 : Tm · (Π (U lzero) (Π (Π 𝟘 (U lzero)) (Π (Π 𝟙 (𝟙 $ 𝟘)) (Π 𝟚 (𝟚 $ 𝟘)))))
  -- test2 = lam (lam (lam (lam (𝟙 $ 𝟘))))

  -- Application, but write El explicitly
  -- test3 : Tm · 
  --   (Π (U 0) 
  --   (Π (Π (El 𝟘) (U 0)) 
  --   (Π (Π (El 𝟙) (((El (𝟙 $ 𝟘))))) 
  --   (Π (El 𝟚) (El (𝟚 $ 𝟘))))))
  -- test3 = lam (lam (lam (lam (𝟙 $ 𝟘))))

  -- Seeing untypeable things, Agda says it fails to solve some constraints,
  -- meaning that it is impossible to find a type for this thing.
  -- test4 = q $ q

  test4 : Tm · (Π (U 1) (Π (↑T (El 𝟘)) (↑T (El 𝟙))))
  test4 = lam (lam 𝟘) 

  test5 : ∀{n}{A : Type (b.suc n)} → Tm · (λ _ → `Π A (λ _ → A))
  test5 = lam 𝟘


module StackExamples where

  open b using (ℕ; _+'_)
  open Machine.Value
  open Machine.Config
  open Machine.Theory
  open Examples.ShallowDFC
  
  -- Adding numbers
  test1 : Is D ◆ ◆ (◆ ∷ (nat 5))
  test1 = 
       CLO 0 Add
    >> LIT 2 
    >> APP
    >> LIT 3
    >> APP
    >> RET

  -- Identity  (A : Set0, x : A)
  test2 : Is D (◆ ∷ U0 ∷ (El 𝟘)) (◆ ∷ 𝟘) (◆ ∷ 𝟘)
  test2 = 
       CLO 0 Iden
    >> VAR V₁
    >> APP
    >> DOWN
    >> SWP
    >> APP
    >> RET

  -- Using Iden0
  test3 : Is D (◆ ∷ U0 ∷ (El 𝟘)) ◆ (◆ ∷ 𝟘)
  test3 =
       VAR V₁
    >> CLO 1 Iden0
    >> VAR V₀
    >> APP
    >> RET

  -- Adding numbers via App
  test4 : ∀{x y : ℕ} → Is D ◆ ◆ (◆ ∷ nat (x +' y))
  test4 {x} {y} = 
       CLO 0 App
    >> TLIT Nat
    >> APP
    >> CLO 0 LNat
    >> APP
    >> DOWN
    >> CLO 0 Add
    >> LIT x
    >> APP
    >> APP
    >> LIT y
    >> APP
    >> RET

  -- Adding numbers, via App, using the most-curried version only
  test5 : ∀{x y : ℕ} → Is D ◆ ◆ (◆ ∷ nat (x +' y))
  test5 {x} {y} = 
       TLIT Nat 
    >> CLO 0 LNat 
    >> LIT x 
    >> CLO 1 Add0 
    >> CLO 3 App0 
    >> LIT y 
    >> APP
    >> RET
    
  -- Example included in TYPES2025 abstract
  test-TYPES : Is D ◆ ◆ (◆ ∷ nat 5)
  test-TYPES = 
       TLIT Nat
    >> CLO 0 LNat 
    >> LIT 2 
    >> CLO 1 Add0 
    >> CLO 3 App0 
    >> LIT 3 
    >> APP 
    >> RET
  
  run = Exec 100 impl test-TYPES (lit-n 5) 

open Machine.Config
open Machine.Step
open Machine.Value

