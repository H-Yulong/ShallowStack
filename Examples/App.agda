module App where

open import Agda.Primitive
import Basic as lib
open import Shallow

A : Ty · _
A = U0

C2 : Con _
C2 = · ▹ A

----

B : Ty C2 _
B = (Π 𝟘 U0)

C1 : Con _
C1 = C2 ▹ B

----

Tf : Ty C1 _
Tf = Π 𝟙 (𝟙 $ 𝟘)

C0 : Con _
C0 = C1 ▹ Tf
