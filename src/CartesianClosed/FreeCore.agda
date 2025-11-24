module CartesianClosed.FreeCore where

open import Cubical.Foundations.Prelude

private
  variable
    ℓ : Level
    A : Type ℓ

infixr 5 _⇒_
infixr 6 _*_

--------------------------------------------------------------------------------

data FreeCore (A : Type ℓ) : Type ℓ where
  ι : A → FreeCore A
  ⊤ : FreeCore A
  _*_ : (t u : FreeCore A) → FreeCore A
  _⇒_ : (t u : FreeCore A) → FreeCore A

  *-identityˡ : ∀ t → ⊤ * t ≡ t
  *-identityʳ : ∀ t → t * ⊤ ≡ t
  *-comm : ∀ t u → t * u ≡ u * t
  *-assoc : ∀ t u v → (t * u) * v ≡ t * (u * v)

  ⇒-identityˡ : ∀ t → t ≡ ⊤ ⇒ t
  ⇒-curry : ∀ t u v → t ⇒ u ⇒ v ≡ (t * u) ⇒ v
  ⇒-annihilʳ : ∀ t → t ⇒ ⊤ ≡ ⊤
  ⇒-distribˡ : ∀ t u v → t ⇒ (u * v) ≡ (t ⇒ u) * (t ⇒ v)

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

  -- TODO: Add more coherence laws

  trunc : ∀ t u (p q : t ≡ u) (P Q : p ≡ q) → P ≡ Q
