module Model.Context where

open import Agda.Primitive
open import Lib.Basic using (ℕ; zero; suc)
open import Model.Shallow hiding (zero; suc)

infixl 5 _∷_

private variable
  i j k i' j' k' : Level
  Γ : Con i
  A : Ty Γ j
  B : Ty (Γ ▹ A) k
  C : Ty (Γ ▹ A ▹ B) i'
  D : Ty (Γ ▹ A ▹ B ▹ C) j'
  l m n : ℕ

-- Deeper shallow embedded context,
-- useful for accessing runtime environments

data Ctx : Con i → ℕ → Setω where
  ◆ : Ctx · 0
  _∷_ : Ctx Γ n → (A : Ty Γ j) → Ctx (Γ ▹ A) (suc n)

private variable
  sΓ : Ctx Γ l

-- Literal variables, essentially Fin
data V : (sΓ : Ctx Γ n) → (A : Ty Γ j) → Setω where
  --
  vz : V (sΓ ∷ A) (A [ p ]T) 
  --
  vs : {B : Ty Γ k} → V sΓ A → V (sΓ ∷ B) (A [ p ]T) 
  --

⟦_⟧V : V sΓ A → Var Γ A 
⟦ vz ⟧V = 𝟘
⟦ vs v ⟧V = 𝕤 ⟦ v ⟧V

-- Variable names

V₀ : V (sΓ ∷ A) (A [ p ]T)
V₀ = vz

V₁ : V (sΓ ∷ A ∷ B) (A [ p² ]T)
V₁ = vs vz

V₂ : V (sΓ ∷ A ∷ B ∷ C) (A [ p³ ]T)
V₂ = vs (vs vz)

V₃ : V (sΓ ∷ A ∷ B ∷ C ∷ D) (A [ p⁴ ]T)
V₃ = vs (vs (vs vz))
