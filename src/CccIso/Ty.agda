module CccIso.Ty where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Data.Fin.Recursive.Base using (Fin)
open import Cubical.Data.Nat.Base using (ℕ)

infixr 5 _⇒_
infixr 6 _*_

--------------------------------------------------------------------------------

data Ty (n : ℕ) : Type where
  ι   : (x : Fin n) → Ty n
  ⊤   : Ty n
  _*_ : (A B : Ty n) → Ty n
  _⇒_ : (A B : Ty n) → Ty n

  *-identityˡ : ∀ A → ⊤ * A ≡ A
  *-identityʳ : ∀ A → A * ⊤ ≡ A
  *-comm      : ∀ A B → A * B ≡ B * A
  *-assoc     : ∀ A B C → (A * B) * C ≡ A * (B * C)

  ⇒-identityˡ : ∀ A → A ≡ ⊤ ⇒ A
  ⇒-curry     : ∀ A B C → A ⇒ (B ⇒ C) ≡ (A * B) ⇒ C
  ⇒-annihilʳ  : ∀ A → A ⇒ ⊤ ≡ ⊤
  ⇒-distribˡ  : ∀ A B C → A ⇒ (B * C) ≡ (A ⇒ B) * (A ⇒ C)

  -- TODO: add coherence laws

  *-pentagon : ∀ A B C D →
    Path (((A * B) * C) * D ≡ A * (B * (C * D)))
      (*-assoc (A * B) C D ∙ *-assoc A B (C * D))
      (cong (_* D) (*-assoc A B C) ∙∙ *-assoc A (B * C) D ∙∙ cong (A *_) (*-assoc B C D))

  *-triangle : ∀ A B →
    Square
      (*-assoc A ⊤ B)
      (cong (_* B) (*-identityʳ A))
      refl
      (cong (A *_) (*-identityˡ B))

  *-hexagon : ∀ A B C →
    Path ((A * B) * C ≡ B * (C * A))
      (*-assoc A B C ∙∙ *-comm A (B * C) ∙∙ *-assoc B C A)
      (cong (_* C) (*-comm A B) ∙∙ *-assoc B A C ∙∙ cong (B *_) (*-comm A C))

  *-bigon : ∀ A B → *-comm A B ≡ sym (*-comm B A)

  -- only groupoid truncate to allow interpretation into hSet
  trunc : ∀ A B (p q : A ≡ B) (P Q : p ≡ q) → P ≡ Q
