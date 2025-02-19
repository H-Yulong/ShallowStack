module Examples.Compose where

open import Agda.Primitive
import Lib.Basic as lib
open import Model.Shallow

A : Ty · _
A = U0

C4 : Con _
C4 = · ▹ A

----

B : Ty C4 _
B = Π 𝟘 U0

C3 : Con _
C3 = C4 ▹ B

----

C : Ty C3 _
C = Π 𝟙 (Π (𝟙 $ 𝟘) U0) 

C2 : Con _
C2 = C3 ▹ C

----

Tg : Ty C2 _
Tg = Π 𝟚 (Π (𝟚 $ 𝟘) (𝟚 $ 𝟙 $ 𝟘)) 

C1 : Con _
C1 = C2 ▹ Tg

----

Tf : Ty C1 _
Tf = Π 𝟛 (𝟛 $ 𝟘)

C0 : Con _
C0 = C1 ▹ Tf

---- 

Tx : Ty C0 _
Tx = q [ p⁴ ]

Cxfx : Ty (C0 ▹ Tx) _
Cxfx = 𝟛 $ 𝟘 $ (𝟙 $ 𝟘)
