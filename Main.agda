module Main where

import Basic as lib

-- Main agda files
open import Shallow
open import ShallowDFC
open import Stack

-- Tests and notes
import App
import Compose
import Performance

-- Examples of the source language,
-- shallow-embedded Martin-Löf type theory
module SourceExamples where

  open import Agda.Primitive
  
  -- Identity
  test1 : Tm · (Π (U lzero) (Π 𝟘 𝟙))
  test1 = lam (lam 𝟘) 

  -- Application
  -- It takes a while to check this
  -- Might take even longer to check full dependent composition
  test2 : Tm · (Π (U lzero) (Π (Π 𝟘 (U lzero)) (Π (Π 𝟙 (𝟙 $ 𝟘)) (Π 𝟚 (𝟚 $ 𝟘)))))
  test2 = lam (lam (lam (lam (𝟙 $ 𝟘))))

  -- Application, but write El explicitly
  test3 : Tm · 
    (Π (U lzero) 
    (Π (Π (El 𝟘) (U lzero)) 
    (Π (Π (El 𝟙) (((El (𝟙 $ 𝟘))))) 
    (Π (El 𝟚) (El (𝟚 $ 𝟘))))))
  test3 = lam (lam (lam (lam (𝟙 $ 𝟘))))

  -- Seeing untypeable things, Agda says it fails to solve some constraints,
  -- meaning that it is impossible to find a type for this thing.
  -- test4 = q $ q

  test4 : Tm · (Π (U (lsuc lzero)) (Π 𝟘 𝟙))
  test4 = lam (lam 𝟘) 

  test5 : Tm · (λ _ → Set → Set)
  test5 = lam 𝟘

module StackExamples where

  open lib using (ℕ; _+'_)

  -- Adding numbers
  t1 : Is {Γ = ·} ◆ (◆ ∷ (nat 5))
  t1 = 
      CLO 0 Add
    >> LIT 2 
    >> APP
    >> LIT 3
    >> APP

  -- Identity
  t2 : Is {Γ = · ▹ U0 ▹ 𝟘} (◆ ∷ 𝟘) (◆ ∷ 𝟘)
  t2 = 
      CLO 0 Id
    >> TLIT 𝟙
    >> APP
    >> SWP
    >> APP

  -- Using Id0
  t3 : Is {Γ = · ▹ U0 ▹ 𝟘} (◆ ∷ 𝟘) (◆ ∷ 𝟘)
  t3 =
      TLIT 𝟙
    >> CLO 1 Id0
    >> SWP 
    >> APP

  -- Adding numbers via App
  t4 : ∀{x y : ℕ} → Is {Γ = ·} ◆ (◆ ∷ nat (x +' y))
  t4 {x} {y} = 
      CLO 0 App
    >> TLIT Nat
    >> APP
    >> CLO 0 LNat
    >> APP
    >> CLO 0 Add
    >> LIT x
    >> APP
    >> APP
    >> LIT y
    >> APP

  -- Adding numbers, via App, using the most-curried version only
  t5 : ∀{x y : ℕ} → Is {Γ = ·} ◆ (◆ ∷ nat (x +' y))
  t5 {x} {y} = 
      TLIT Nat 
    >> CLO 0 LNat 
    >> LIT x 
    >> CLO 1 Add0 
    >> CLO 3 App0 
    >> LIT y 
    >> APP
 