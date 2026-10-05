module Model.Context where

open import Agda.Primitive
open import Lib.Basic using (ℕ; zero; suc)
open import Lib.Order
open import Model.Shallow hiding (zero; suc)

infixl 5 _∷_

private variable
  Γ : Con
  len i j k l m n : ℕ

data Ctx : Con → ℕ → Set₁ where
  ◆ : Ctx · 0
  _∷_ : Ctx Γ len → (A : Ty Γ n) → Ctx (Γ ▹ A) (suc len)

private variable
  sΓ : Ctx Γ len

-- Literal variables, essentially Fin
data V : (sΓ : Ctx Γ len) → (A : Ty Γ n) → Set₁ where
  vz : {A : Ty Γ n} → V (sΓ ∷ A) (A [ p ]T) 
  vs : {A : Ty Γ n}{B : Ty Γ m} → V sΓ A → V (sΓ ∷ B) (A [ p ]T) 

⟦_⟧V : {A : Ty Γ n} → V sΓ A → Var Γ A 
⟦ vz ⟧V = 𝟘
⟦ vs v ⟧V = 𝕤 ⟦ v ⟧V

-- Variable names

V₀ : {A : Ty Γ n} → V (sΓ ∷ A) (A [ p ]T)
V₀ = vz

V₁ : 
    {A : Ty Γ n}
    {B : Ty (Γ ▹ A) m} → 
  V (sΓ ∷ A ∷ B) (A [ p² ]T)
V₁ = vs vz

V₂ : 
    {A : Ty Γ n}
    {B : Ty (Γ ▹ A) m}
    {C : Ty (Γ ▹ A ▹ B) l} → 
  V (sΓ ∷ A ∷ B ∷ C) (A [ p³ ]T)
V₂ = vs (vs vz)

V₃ : 
    {A : Ty Γ n}
    {B : Ty (Γ ▹ A) m}
    {C : Ty (Γ ▹ A ▹ B) l} 
    {D : Ty (Γ ▹ A ▹ B ▹ C) k} →
  V (sΓ ∷ A ∷ B ∷ C ∷ D) (A [ p⁴ ]T)
V₃ = vs (vs (vs vz))
 