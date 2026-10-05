module DAM.Examples.Vector.Zip.Source where

open import Lib.Order
open import Model.Context
open import Model.Shallow
open import DAM.Examples.Vector.Vec

Δ : Con
Δ = · ▹ U0 ▹ U0 ▹ Nat ▹ Vec 𝟚 𝟘

sΔ : Ctx Δ _
sΔ = ◆ ∷ U0 ∷ U0 ∷ Nat ∷ Vec 𝟚 𝟘

AxB : Ty (Δ ▹ Vec 𝟚 𝟙) 0
AxB = Σ (El (𝟛 [ p ])) (El (𝟛 [ p ]))

ΔP : Con
ΔP = Δ ▹ Vec 𝟚 𝟙 ▹ Nat

P : Ty ΔP 0
P = Π (Vec (𝟛 [ p² ]) 𝟘) (Π (Vec (𝟛 [ p² ]) 𝟙) (Vec (c (Σ (El (𝟛 [ p⁴ ])) (El (𝟛 [ p⁴ ])))) 𝟚))

Δz : Con
Δz = Δ ▹ Vec 𝟚 𝟙 ▹ ⊤  

Az : Ty Δz 0
Az = Vec (𝟛 [ p² ]) zero

Bz : Ty (Δz ▹ Az) 0
Bz = Vec (𝟛 [ p² ]) zero

ABz : Ty (Δz ▹ Az ▹ Bz) 0
ABz = Vec (c (Σ (El (𝟛 [ p⁴ ])) (El (𝟛 [ p⁴ ])))) zero 

Δs : Con
Δs = Δ ▹ Vec 𝟚 𝟙 ▹ Nat ▹ P

As : Ty Δs 0
As = Vec (𝟛 [ p³ ]) (suc 𝟙) 

Bs : Ty (Δs ▹ As) 0
Bs = Vec (𝟛 [ p³ ]) (suc 𝟚)

ABs : Ty (Δs ▹ As ▹ Bs) 0
ABs = Vec (c (Σ (El (𝟛 [ p⁵ ]) ) (El (𝟛 [ p⁵ ])))) (suc 𝟛)


