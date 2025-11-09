module CccIso.NF where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.GroupoidLaws using (cong-∙∙)
open import Cubical.Foundations.Path using (Square→compPath)
open import Cubical.Data.Fin.Recursive.Base using (Fin)
open import Cubical.Data.Nat.Base using (ℕ)

private
  variable
    n : ℕ

infixr 5 _⇒ᵃ_ _⇒ᶠ_ _⇒_
infixr 6 _*ᶠ_ _*_

--------------------------------------------------------------------------------

data Atom (n : ℕ) : Type
data Factor (n : ℕ) : Type
data NF (n : ℕ) : Type

data Atom n where
  var : (x : Fin n) → Atom n
  [_] : (ν : NF n) → Atom n

data Factor n where
  _⇒ᵃ_ : (ν : NF n) (α : Atom n) → Factor n

-- Bag of factors
data NF n where
  ⊤    : NF n
  _*ᶠ_ : (φ : Factor n) (ν : NF n) → NF n

  swap : ∀ φ ψ ν → φ *ᶠ ψ *ᶠ ν ≡ ψ *ᶠ φ *ᶠ ν

  -- swap is involutive
  invol : ∀ φ ψ ν → swap φ ψ ν ≡ sym (swap ψ φ ν)

  -- identify the two different paths from ε * φ * ψ * ν to ψ * φ * ε * ν
  hexagon : ∀ ε φ ψ ν →
    Path (ε *ᶠ φ *ᶠ ψ *ᶠ ν ≡ ψ *ᶠ φ *ᶠ ε *ᶠ ν)
      (swap ε φ (ψ *ᶠ ν) ∙∙ cong (φ *ᶠ_) (swap ε ψ ν) ∙∙ swap φ ψ (ε *ᶠ ν))
      (cong (ε *ᶠ_) (swap φ ψ ν) ∙∙ swap ε ψ (φ *ᶠ ν) ∙∙ cong (ψ *ᶠ_) (swap ε φ ν))

  -- only groupoid truncate to allow interpretation into hSet
  trunc : ∀ ν μ (p q : ν ≡ μ) (P Q : p ≡ q) → P ≡ Q

-- Smart constructors

record _⊂_ (X Y : ℕ → Type) : Type where
  field ↑_ : X n → Y n

open _⊂_ ⦃ ... ⦄ public

instance
  Atom⊂Factor : Atom ⊂ Factor
  Atom⊂Factor .↑_ = ⊤ ⇒ᵃ_

  Factor⊂NF : Factor ⊂ NF
  Factor⊂NF .↑_ = _*ᶠ ⊤

  Atom⊂NF : Atom ⊂ NF
  Atom⊂NF .↑_ α = (⊤ ⇒ᵃ α) *ᶠ ⊤

--------------------------------------------------------------------------------
-- Product and exponential for NF

{-# TERMINATING #-}
_*_ : NF n → NF n → NF n
⊤ * μ = μ
(φ *ᶠ ν) * μ = φ *ᶠ (ν * μ)
swap φ ψ ν i * μ = swap φ ψ (ν * μ) i
invol φ ψ ν i j * μ = invol φ ψ (ν * μ) i j
hexagon ε φ ψ ν i j * μ = path i j
  where
    path : Path (ε *ᶠ φ *ᶠ ψ *ᶠ ν * μ ≡ ψ *ᶠ φ *ᶠ ε *ᶠ ν * μ)
      (cong (_* μ) (swap ε φ (ψ *ᶠ ν) ∙∙ cong (φ *ᶠ_) (swap ε ψ ν) ∙∙ swap φ ψ (ε *ᶠ ν)))
      (cong (_* μ) (cong (ε *ᶠ_) (swap φ ψ ν) ∙∙ swap ε ψ (φ *ᶠ ν) ∙∙ cong (ψ *ᶠ_) (swap ε φ ν)))
    path = cong-∙∙ (_* μ) _ _ _ ∙∙ hexagon ε φ ψ (ν * μ) ∙∙ sym (cong-∙∙ (_* μ) _ _ _)
trunc ν ι p q P Q i j k * μ =
  trunc
    (ν * μ) (ι * μ)
    (λ i → p i * μ) (λ i → q i * μ)
    (λ i j → P i j * μ) (λ i j → Q i j * μ)
    i j k

-- uncurry
_⇒ᶠ_ : NF n → Factor n → Factor n
ν ⇒ᶠ (μ ⇒ᵃ α) = (ν * μ) ⇒ᵃ α

-- distribute exponential over products
{-# TERMINATING #-}
_⇒_ : NF n → NF n → NF n
ν ⇒ ⊤ = ⊤
ν ⇒ (φ *ᶠ μ) = (ν ⇒ᶠ φ) *ᶠ (ν ⇒ μ)
ν ⇒ swap φ ψ μ i = swap (ν ⇒ᶠ φ) (ν ⇒ᶠ ψ) (ν ⇒ μ) i
ν ⇒ invol φ ψ μ i j = invol (ν ⇒ᶠ φ) (ν ⇒ᶠ ψ) (ν ⇒ μ) i j
ν ⇒ hexagon ε φ ψ μ i j = path i j
  where
    path : Path ((ν ⇒ᶠ ε) *ᶠ (ν ⇒ᶠ φ) *ᶠ (ν ⇒ᶠ ψ) *ᶠ (ν ⇒ μ) ≡ (ν ⇒ᶠ ψ) *ᶠ (ν ⇒ᶠ φ) *ᶠ (ν ⇒ᶠ ε) *ᶠ (ν ⇒ μ))
      (cong (ν ⇒_) (swap ε φ (ψ *ᶠ μ) ∙∙ cong (φ *ᶠ_) (swap ε ψ μ) ∙∙ swap φ ψ (ε *ᶠ μ)))
      (cong (ν ⇒_) (cong (ε *ᶠ_) (swap φ ψ μ) ∙∙ swap ε ψ (φ *ᶠ μ) ∙∙ cong (ψ *ᶠ_) (swap ε φ μ)))
    path = cong-∙∙ (ν ⇒_) _ _ _ ∙∙ hexagon (ν ⇒ᶠ ε) (ν ⇒ᶠ φ) (ν ⇒ᶠ ψ) (ν ⇒ μ) ∙∙ sym (cong-∙∙ (ν ⇒_) _ _ _)
ν ⇒ trunc μ ι p q P Q i j k =
  trunc
    (ν ⇒ μ) (ν ⇒ ι)
    (λ i → ν ⇒ p i) (λ i → ν ⇒ q i)
    (λ i j → ν ⇒ P i j) (λ i j → ν ⇒ Q i j)
    i j k
