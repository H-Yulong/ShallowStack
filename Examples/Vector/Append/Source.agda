module Examples.Vector.Append.Source where

open import Lib.Order
open import Model.Context
open import Model.Shallow
open import Examples.Vector.Vec

Δ : Con
Δ = · ▹ U0 ▹ Nat ▹ Nat ▹ Vec 𝟚 𝟙

sΔ : Ctx Δ _
sΔ = ◆ ∷ U0 ∷ Nat ∷ Nat ∷ Vec 𝟚 𝟙

ΔP : Con
ΔP = Δ ▹ Vec 𝟛 𝟙 ▹ Nat

P : Ty ΔP 0
P = Π (Vec (𝟛 [ p² ]) 𝟘) (Vec (𝟛 [ p³ ]) (add 𝟙 (𝟛 [ p ])))

Δz : Con
Δz = Δ ▹ Vec 𝟛 𝟙 ▹ ⊤  

Az : Ty Δz 0
Az = (Vec (𝟛 [ p² ]) zero)

Bz : Ty (Δz ▹ Az) 0
Bz = (Vec (𝟛 [ p³ ]) (𝟛 [ p ]))

Δs : Con
Δs = Δ ▹ Vec 𝟛 𝟙 ▹ Nat ▹ P

As : Ty Δs 0
As = Vec (𝟛 [ p³ ]) (suc 𝟙) 

Bs : Ty (Δs ▹ As) 0
Bs = Vec (𝟛 [ p⁴ ]) (suc (add 𝟚 (𝟛 [ p² ])))

