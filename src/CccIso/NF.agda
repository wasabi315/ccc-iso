module CccIso.NF where

open import Cubical.Foundations.Prelude
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

  -- Avoiding as possible path concatenation in the type of the
  -- coherence laws, but no way to avoid it for hexagon.

  -- swap is involutive
  invol : ∀ φ ψ ν → swap φ ψ ν ≡ sym (swap ψ φ ν)

  -- independent swaps commute
  square : ∀ ε φ ψ γ ν →
    Square
      (swap ε φ (ψ *ᶠ γ *ᶠ ν))
      (swap ε φ (γ *ᶠ ψ *ᶠ ν))
      (cong (λ μ → ε *ᶠ φ *ᶠ μ) (swap ψ γ ν))
      (cong (λ μ → φ *ᶠ ε *ᶠ μ) (swap ψ γ ν))

  -- identify the two different paths from ε * φ * ψ * ν to ψ * φ * ε * ν
  hexagon : ∀ ε φ ψ ν →
    Path (ε *ᶠ φ *ᶠ ψ *ᶠ ν ≡ ψ *ᶠ φ *ᶠ ε *ᶠ ν)
      (swap ε φ (ψ *ᶠ ν) ∙∙ cong (φ *ᶠ_) (swap ε ψ ν) ∙∙ swap φ ψ (ε *ᶠ ν))
      (cong (ε *ᶠ_) (swap φ ψ ν) ∙∙ swap ε ψ (φ *ᶠ ν) ∙∙ cong (ψ *ᶠ_) (swap ε φ ν))

  -- only groupoid truncate to allow interpretation into hSet
  trunc : isGroupoid (NF n)

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

{-
        φ ψ ν ================= φ ψ ν
        //∥                     // |
       // ∥                    //  |
      //  ∥                   //   |
    φ ψ ν ----------------> φ ψ ν  | swap ψ φ ν k
     (swap φ ψ ν ∙ swap ψ φ ν) i   |
     ∥    ∥                   |    |
     ∥    ∥   swap ψ φ ν (~i) |    |
     ∥  φ ψ ν ----------------| ψ φ ν
     ∥   //      swap ψ φ ν k |  //             k
     ∥  //                    | //              ^ j
     ∥ //                     |//               |/
    φ ψ ν ----------------> ψ φ ν               ∙-----> i
           swap φ ψ ν i
-}
invol' : (φ ψ : Factor n) (ν : NF n) → swap φ ψ ν ∙ swap ψ φ ν ≡ refl
invol' φ ψ ν j i =
  hcomp
    (λ where
      k (i = i0) → φ *ᶠ ψ *ᶠ ν
      k (i = i1) → swap ψ φ ν k
      k (j = i0) → compPath-filler (swap φ ψ ν) (swap ψ φ ν) k i
      k (j = i1) → swap ψ φ ν (~ i ∨ k))
    (invol φ ψ ν j i)

square' : (ε φ ψ γ : Factor n) (ν : NF n) →
    cong (λ μ → ε *ᶠ φ *ᶠ μ) (swap ψ γ ν) ∙ swap ε φ (γ *ᶠ ψ *ᶠ ν)
  ≡ swap ε φ (ψ *ᶠ γ *ᶠ ν) ∙ cong (λ μ → φ *ᶠ ε *ᶠ μ) (swap ψ γ ν)
square' ε φ ψ γ ν = Square→compPath (square ε φ ψ γ ν)

--------------------------------------------------------------------------------
-- Product and exponential for NF

_*_ : NF n → NF n → NF n
⊤ * μ = μ
(φ *ᶠ ν) * μ = φ *ᶠ (ν * μ)
swap φ ψ ν i * μ = swap φ ψ (ν * μ) i
invol φ ψ ν i j * μ = invol φ ψ (ν * μ) i j
square ε φ ψ γ ν i j * μ = square ε φ ψ γ (ν * μ) i j
hexagon ε φ ψ ν i j * μ =
  hcomp
    (λ where
      k (i = i0) → {!   !}
      k (i = i1) → {!   !}
      k (j = i0) → ε *ᶠ φ *ᶠ ψ *ᶠ ν * μ
      k (j = i1) → ψ *ᶠ φ *ᶠ ε *ᶠ ν * μ)
    (hexagon ε φ ψ (ν * μ) i j)
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
_⇒_ : NF n → NF n → NF n
ν ⇒ ⊤ = ⊤
ν ⇒ (φ *ᶠ μ) = (ν ⇒ᶠ φ) *ᶠ (ν ⇒ μ)
ν ⇒ swap φ ψ μ i = swap (ν ⇒ᶠ φ) (ν ⇒ᶠ ψ) (ν ⇒ μ) i
ν ⇒ invol φ ψ μ i j = invol (ν ⇒ᶠ φ) (ν ⇒ᶠ ψ) (ν ⇒ μ) i j
ν ⇒ square ε φ ψ γ μ i j =
  square (ν ⇒ᶠ ε) (ν ⇒ᶠ φ) (ν ⇒ᶠ ψ) (ν ⇒ᶠ γ) (ν ⇒ μ) i j
ν ⇒ hexagon ε φ ψ μ i j =
  hcomp
    (λ where
      k (i = i0) → {!   !}
      k (i = i1) → {!   !}
      k (j = i0) → (ν ⇒ᶠ ε) *ᶠ (ν ⇒ᶠ φ) *ᶠ (ν ⇒ᶠ ψ) *ᶠ (ν ⇒ μ)
      k (j = i1) → (ν ⇒ᶠ ψ) *ᶠ (ν ⇒ᶠ φ) *ᶠ (ν ⇒ᶠ ε) *ᶠ (ν ⇒ μ))
    (hexagon (ν ⇒ᶠ ε) (ν ⇒ᶠ φ) (ν ⇒ᶠ ψ) (ν ⇒ μ) i j)
ν ⇒ trunc μ ι p q P Q i j k =
  trunc
    (ν ⇒ μ) (ν ⇒ ι)
    (λ i → ν ⇒ p i) (λ i → ν ⇒ q i)
    (λ i j → ν ⇒ P i j) (λ i j → ν ⇒ Q i j)
    i j k
