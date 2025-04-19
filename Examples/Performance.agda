module Examples.Performance where

open import Agda.Primitive
import Lib.Basic as lib
open import Model.Shallow

-- This file shows that the performance overhead
-- mainly comes from elaboration.

-- unit: seconds

{-
T1 : Tm · Nat
T1 = 
  (lam 𝟘 $ -- 0.249
  lam 𝟘 $ -- 0.360
  lam 𝟘 $ -- 1.047
  lam 𝟘 $ -- 4.879
  lam 𝟘 $ -- 57.411
  -- Doesn't matter below
  lam 𝟘 $
  lam 𝟘 $
  lam 𝟘 $
  -- lam 𝟘 $
  -- lam 𝟘 $
  (lam 𝟘)) $ zero -- 0.247 
-}

{-
T2 : Tm · Nat
T2 = 
  (lam {A = Π Nat Nat} 𝟘 $ -- 0.232
  lam {A = Π Nat Nat} 𝟘 $ -- 0.266
  lam {A = Π Nat Nat} 𝟘 $ -- 0.285
  lam {A = Π Nat Nat} 𝟘 $ -- 0.281
  lam {A = Π Nat Nat} 𝟘 $ -- 0.343
  lam {A = Π Nat Nat} 𝟘 $ -- 0.297
  lam {A = Π Nat Nat} 𝟘 $ -- 0.360
  lam {A = Π Nat Nat} 𝟘 $ -- 0.300
  lam {A = Π Nat Nat} 𝟘 $ -- 0.466
  lam {A = Π Nat Nat} 𝟘 $ -- 0.479
  (lam 𝟘)) $ zero -- 0.247 
-}


 