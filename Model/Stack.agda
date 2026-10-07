module Model.Stack where

open import Agda.Primitive
import Lib.Basic as b 

open import Lib.Order

open import Model.Universe hiding (⟦_⟧)
open import Model.Shallow
open import Model.Context

open b using (ℕ; _+_)

infixl 5 _∷_
-- infixr 20 _>>_

private variable
  m n ms ns len len' id id' : ℕ  
  Γ : Con

data Stack (Γ : Con) : ℕ → Set₁ where
  ◆ : Stack Γ 0
  _∷_ : ∀{A : Ty Γ n} → Stack Γ ns → Tm Γ A → Stack Γ (b.suc ns)

-- Stack typing & interpretation of stacks into substitutions
mutual
  data _⊢_of_as_ {Γ : Con} (sΓ : Ctx Γ len) : ∀{Δ} → Stack Γ ns → Ctx Δ len' → Sub Γ Δ → Set₁ where
    instance
      nil : sΓ ⊢ ◆ of ◆ as ε
      cons : 
        ∀ {Δ}{sΔ : Ctx Δ len'}{A : Ty Δ n}
          {σ : Stack Γ ns}{δ : Sub Γ Δ}{t : Tm Γ (A [ δ ]T)} → 
          ⦃ pf : sΓ ⊢ σ of sΔ as δ ⦄ → 
        sΓ ⊢ (σ ∷ t) of (sΔ ∷ A) as (δ ▻ t)

-- Some stack operations: append, take, drop
_++_ : Stack Γ ms → Stack Γ ns → Stack Γ (ns + ms)
σ ++ ◆ = σ
σ ++ (σ' ∷ x) = (σ ++ σ') ∷ x

take : (ns : b.ℕ) (σ : Stack Γ (ns + ms)) → Stack Γ ns
take b.zero σ = ◆
take (b.suc ns) (σ ∷ x) = (take ns σ) ∷ x

drop : (ns : b.ℕ) (σ : Stack Γ (ns + ms)) → Stack Γ ms
drop b.zero σ = σ
drop (b.suc ns) (σ ∷ x) = drop ns σ

-- Stack look-up, which is essentially Fin / de-Bruijn variables
data SVar {Γ : Con} : Stack Γ ns → Ty Γ n → Set₁ where
  --
  vz : {A : Ty Γ n}{σ : Stack Γ ns}{t : Tm Γ A} → SVar (σ ∷ t) A
  --
  vs : 
    {A A' : Ty Γ n}{σ : Stack Γ ns}{t : Tm Γ A'} →  
    SVar σ A → SVar (σ ∷ t) A

find : {A : Ty Γ n}(σ : Stack Γ ns) (t : SVar σ A) → Tm Γ A
find (σ ∷ t) vz = t
find (σ ∷ t) (vs x) = find σ x

-- Substitution on stacks
_[_]st : ∀{Δ} → Stack Δ ns → Sub Γ Δ → Stack Γ ns
◆ [ ρ ]st = ◆
(σ ∷ t) [ ρ ]st = (σ [ ρ ]st) ∷ t [ ρ ]
