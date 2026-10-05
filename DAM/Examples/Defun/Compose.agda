module DAM.Examples.Defun.Compose where

open import Lib.Order
open import Model.Shallow

A : Ty · _
A = U0

C4 : Con
C4 = · ▹ A

----

B : Ty C4 1
B =  Π (↑T (El 𝟘)) U0

C3 : Con
C3 = C4 ▹ B

----

C : Ty C3 1
C = Π (↑T (El 𝟙)) (Π (↑T (El (𝟙 $ 𝟘))) U0)
-- Π 𝟙 (Π (𝟙 $ 𝟘) U0)

C2 : Con
C2 = C3 ▹ C

----

Tg : Ty C2 0
Tg = Π (El 𝟚) (Π (El (𝟚 $ ↑! 𝟘)) (El (𝟚 $ ↑ 𝟙 $ ↑ 𝟘)))
-- Π 𝟚 (Π (𝟚 $ 𝟘) (𝟚 $ 𝟙 $ 𝟘)) 

C1 : Con
C1 = C2 ▹ Tg

----

Tf : Ty C1 0
Tf = Π (El 𝟛) (El (𝟛 $ ↑ 𝟘))

C0 : Con
C0 = C1 ▹ Tf

---- 

Tx : Ty C0 0
Tx = El (q [ p⁴ ])

Cxfx : Ty (C0 ▹ Tx) 0 
Cxfx = El (𝟛 $ ↑ 𝟘 $ ↑ (𝟙 $ 𝟘))
