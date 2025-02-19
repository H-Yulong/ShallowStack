module Machine.Theory where

-- dup : 
--   ∀ {D : LCon}
--     {i}{Γ : Con i}
--     {n}{σ : Stack Γ n}
--     {j}{A : Ty Γ j} → 
--     Env D n → SVar σ A → Env D (lib.suc n)
-- dup (env ∷ t) vz = env ∷ t ∷ t
-- dup (env ∷ t) (vs x) = (dup env x) ∷ t
