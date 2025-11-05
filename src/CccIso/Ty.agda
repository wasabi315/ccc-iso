module CccIso.Ty where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Fin.Recursive.Base using (Fin)
open import Cubical.Data.Nat.Base using (ℕ)

private
  variable
    n : ℕ

infixr 5 _⇒_
infixr 6 _*_

--------------------------------------------------------------------------------

data Ty (n : ℕ) : Type where
  var : (x : Fin n) → Ty n
  ⊤   : Ty n
  _*_ : (A B : Ty n) → Ty n
  _⇒_ : (A B : Ty n) → Ty n
  [_] : (A : Ty n) → Ty n

  *-comm  : ∀ A B → A * B ≡ B * A
  *-assoc : ∀ A B C → (A * B) * C ≡ A * (B * C)
  ⇒-curry : ∀ A B C → A ⇒ (B ⇒ C) ≡ (A * B) ⇒ C
  ⇒-dist  : ∀ A B C → A ⇒ (B * C) ≡ (A ⇒ B) * (A ⇒ C)
  *-idl   : ∀ A → ⊤ * A ≡ A
  ⇒-idl   : ∀ A → ⊤ ⇒ A ≡ A
  ⇒-zeror : ∀ A → A ⇒ ⊤ ≡ ⊤

  -- TODO: add coherence laws

  trunc : isGroupoid (Ty n)
