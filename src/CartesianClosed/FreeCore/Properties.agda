module CartesianClosed.FreeCore.Properties where

open import Cubical.Foundations.Prelude

open import CartesianClosed.FreeCore

private
  variable
    ℓ : Level
    A : Type ℓ

--------------------------------------------------------------------------------
-- Basic properties

*-swap : (t u v : FreeCore A) → t * u * v ≡ u * t * v
*-swap t u v = sym (*-assoc t u v) ∙∙ cong (_* v) (*-comm t u) ∙∙ *-assoc u t v

-- *-invol : (t u v : FreeCore A) → *-swap t u v ≡ sym (*-swap u t v)
-- *-invol t u v = {!   !}
