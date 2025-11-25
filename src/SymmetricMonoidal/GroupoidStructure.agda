module SymmetricMonoidal.GroupoidStructure where

open import Cubical.Foundations.Prelude

private
  variable
    ℓ : Level
    A : Type ℓ

--------------------------------------------------------------------------------
-- Groupoid structure

record SymmetricMonoidalGroupoid ℓ : Type (ℓ-suc ℓ) where
  no-eta-equality
  field
    Carrier : Type ℓ
    isGroupoidCarrier : isGroupoid Carrier

    ⊤ : Carrier
    _*_ : (t u : Carrier) → Carrier

    *-identityˡ : ∀ t → ⊤ * t ≡ t
    *-identityʳ : ∀ t → t * ⊤ ≡ t
    *-comm : ∀ t u → t * u ≡ u * t
    *-assoc : ∀ t u v → (t * u) * v ≡ t * (u * v)

    *-bigon : ∀ t u → *-comm t u ≡ sym (*-comm u t)

    *-triangle : ∀ t u →
      Square
        (*-assoc t ⊤ u)
        (cong (_* u) (*-identityʳ t))
        refl
        (cong (t *_) (*-identityˡ u))

    *-pentagon : ∀ t u v w →
      Path (((t * u) * v) * w ≡ t * (u * (v * w)))
        (*-assoc (t * u) v w ∙ *-assoc t u (v * w))
        (cong (_* w) (*-assoc t u v)
          ∙∙ *-assoc t (u * v) w
          ∙∙ cong (t *_) (*-assoc u v w))

    *-hexagon : ∀ t u v →
      Path ((t * u) * v ≡ u * (v * t))
        (*-assoc t u v ∙∙ *-comm t (u * v) ∙∙ *-assoc u v t)
        (cong (_* v) (*-comm t u) ∙∙ *-assoc u t v ∙∙ cong (u *_) (*-comm t v))
