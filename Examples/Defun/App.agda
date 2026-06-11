module Examples.Defun.App where

open import Lib.Order
open import Model.Shallow

A : Ty · 1
A = U0

C2 : Con
C2 = · ▹ A

----

B : Ty C2 1
B = Π (↑T! (El 𝟘)) U0

C1 : Con
C1 = C2 ▹ B

----

Tf : Ty C1 0
Tf = Π (El 𝟙) (El (𝟙 $ ↑! 𝟘))

C0 : Con
C0 = C1 ▹ Tf
 