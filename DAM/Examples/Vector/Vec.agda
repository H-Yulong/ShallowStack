module DAM.Examples.Vector.Vec where

open import Agda.Primitive

import Lib.Basic as b
open import Model.Shallow

private variable
  Γ : Con
  len i j k l m n id : b.ℕ

Vec : Tm Γ U0 → Tm Γ Nat → Ty Γ 0
Vec A n = El (iter U0 (c ⊤) (c (Σ (El (A [ p² ])) (El 𝟙))) n)
