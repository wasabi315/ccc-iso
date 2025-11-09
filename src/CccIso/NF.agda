module CccIso.NF where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.GroupoidLaws using (cong-∙∙)
open import Cubical.Foundations.Path using (Square→compPath)
open import Cubical.Data.Fin.Recursive.Base using (Fin)
open import Cubical.Data.Nat.Base using (ℕ)

infixr 5 _⇒ι_ _⇒ᶠ_ _⇒_
infixr 6 _*ᶠ_ _*_

private
  variable
    n : ℕ

--------------------------------------------------------------------------------

data Factor (n : ℕ) : Type
data NF (n : ℕ) : Type

data Factor n where
  _⇒ι_ : (α : NF n) (x : Fin n) → Factor n

-- Bag of factors
data NF n where
  ⊤    : NF n
  _*ᶠ_ : (φ : Factor n) (α : NF n) → NF n

  swap : ∀ φ ψ α → φ *ᶠ ψ *ᶠ α ≡ ψ *ᶠ φ *ᶠ α

  -- swap is involutive
  invol : ∀ φ ψ α → swap φ ψ α ≡ sym (swap ψ φ α)

  -- identify the two different paths from ε * φ * ψ * ν to ψ * φ * ε * ν
  hexagon : ∀ ε φ ψ α →
    Path (ε *ᶠ φ *ᶠ ψ *ᶠ α ≡ ψ *ᶠ φ *ᶠ ε *ᶠ α)
      (swap ε φ (ψ *ᶠ α) ∙∙ cong (φ *ᶠ_) (swap ε ψ α) ∙∙ swap φ ψ (ε *ᶠ α))
      (cong (ε *ᶠ_) (swap φ ψ α) ∙∙ swap ε ψ (φ *ᶠ α) ∙∙ cong (ψ *ᶠ_) (swap ε φ α))

  -- only groupoid truncate to allow interpretation into hSet
  trunc : ∀ α β (p q : α ≡ β) (P Q : p ≡ q) → P ≡ Q

--------------------------------------------------------------------------------
-- Product and exponential for NF

{-# TERMINATING #-}
_*_ : NF n → NF n → NF n
⊤ * β = β
(φ *ᶠ α) * β = φ *ᶠ (α * β)
swap φ ψ α i * β = swap φ ψ (α * β) i
invol φ ψ α i j * β = invol φ ψ (α * β) i j
hexagon ε φ ψ α i j * β = path i j
  where
    path : Path (ε *ᶠ φ *ᶠ ψ *ᶠ α * β ≡ ψ *ᶠ φ *ᶠ ε *ᶠ α * β)
      (cong (_* β) (swap ε φ (ψ *ᶠ α) ∙∙ cong (φ *ᶠ_) (swap ε ψ α) ∙∙ swap φ ψ (ε *ᶠ α)))
      (cong (_* β) (cong (ε *ᶠ_) (swap φ ψ α) ∙∙ swap ε ψ (φ *ᶠ α) ∙∙ cong (ψ *ᶠ_) (swap ε φ α)))
    path = cong-∙∙ (_* β) _ _ _ ∙∙ hexagon ε φ ψ (α * β) ∙∙ sym (cong-∙∙ (_* β) _ _ _)
trunc α γ p q P Q i j k * β =
  trunc
    (α * β) (γ * β)
    (λ i → p i * β) (λ i → q i * β)
    (λ i j → P i j * β) (λ i j → Q i j * β)
    i j k

-- uncurry
_⇒ᶠ_ : NF n → Factor n → Factor n
α ⇒ᶠ (β ⇒ι x) = (α * β) ⇒ι x

-- distribute exponential over products
{-# TERMINATING #-}
_⇒_ : NF n → NF n → NF n
α ⇒ ⊤ = ⊤
α ⇒ (φ *ᶠ β) = (α ⇒ᶠ φ) *ᶠ (α ⇒ β)
α ⇒ swap φ ψ β i = swap (α ⇒ᶠ φ) (α ⇒ᶠ ψ) (α ⇒ β) i
α ⇒ invol φ ψ β i j = invol (α ⇒ᶠ φ) (α ⇒ᶠ ψ) (α ⇒ β) i j
α ⇒ hexagon ε φ ψ β i j = path i j
  where
    path : Path ((α ⇒ᶠ ε) *ᶠ (α ⇒ᶠ φ) *ᶠ (α ⇒ᶠ ψ) *ᶠ (α ⇒ β) ≡ (α ⇒ᶠ ψ) *ᶠ (α ⇒ᶠ φ) *ᶠ (α ⇒ᶠ ε) *ᶠ (α ⇒ β))
      (cong (α ⇒_) (swap ε φ (ψ *ᶠ β) ∙∙ cong (φ *ᶠ_) (swap ε ψ β) ∙∙ swap φ ψ (ε *ᶠ β)))
      (cong (α ⇒_) (cong (ε *ᶠ_) (swap φ ψ β) ∙∙ swap ε ψ (φ *ᶠ β) ∙∙ cong (ψ *ᶠ_) (swap ε φ β)))
    path = cong-∙∙ (α ⇒_) _ _ _ ∙∙ hexagon (α ⇒ᶠ ε) (α ⇒ᶠ φ) (α ⇒ᶠ ψ) (α ⇒ β) ∙∙ sym (cong-∙∙ (α ⇒_) _ _ _)
α ⇒ trunc β γ p q P Q i j k =
  trunc
    (α ⇒ β) (α ⇒ γ)
    (λ i → α ⇒ p i) (λ i → α ⇒ q i)
    (λ i j → α ⇒ P i j) (λ i j → α ⇒ Q i j)
    i j k
