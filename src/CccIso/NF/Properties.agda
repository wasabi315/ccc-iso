module CccIso.NF.Properties where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
  using (isOfHLevel→isOfHLevelDep; isSet→isGroupoid; isSet→SquareP; isSetΠ2)
open import Cubical.Data.Fin.Recursive.Base using (Fin)
open import Cubical.Data.Nat.Base using (ℕ)

open import CccIso.NF

private
  variable
    n : ℕ
    x y : Fin n
    α β : Atom n
    φ ψ : Factor n
    ν μ : NF n

--------------------------------------------------------------------------------
-- Eliminators

doubleCompPathP : ∀ {a b} {A : Type a} {B : A → Type b} →
  {x y z w : A} {x' : B x} {y' : B y} {z' : B z} {w' : B w} →
  {p : x ≡ y} {q : y ≡ z} {r : z ≡ w} →
  PathP (λ i → B (p i)) x' y' →
  PathP (λ i → B (q i)) y' z' →
  PathP (λ i → B (r i)) z' w' →
  PathP (λ i → B ((p ∙∙ q ∙∙ r) i)) x' w'
doubleCompPathP {B = B} {p = p} {q = q} {r = r} P Q R i =
  comp
    (λ j → B (doubleCompPath-filler p q r j i))
    (λ where
      j (i = i0) → P (~ j)
      j (i = i1) → R j)
    (Q i)

module ElimSetNF {n ℓ} {B : NF n → Type ℓ} (trunc* : ∀ ν → isSet (B ν))
  (⊤* : B ⊤)
  (_**_ : ∀ φ {ν} (ν* : B ν) → B (φ *ᶠ ν))
  (swap* : ∀ φ ψ {ν} (ν* : B ν) →
    PathP (λ i → B (swap φ ψ ν i)) (φ ** (ψ ** ν*)) (ψ ** (φ ** ν*)))
  where

  f : ∀ ν → B ν
  f ⊤ = ⊤*
  f (φ *ᶠ ν) = φ ** f ν
  f (swap φ ψ ν i) = swap* φ ψ (f ν) i
  f (invol φ ψ ν i j) =
    isSet→SquareP (λ i j → trunc* (invol φ ψ ν i j))
      (swap* φ ψ (f ν))
      refl
      (symP (swap* ψ φ (f ν)))
      refl
      i j
  f (square ε φ ψ γ ν i j) =
    isSet→SquareP (λ i j → trunc* (square ε φ ψ γ ν i j))
      (swap* ε φ (ψ ** (γ ** f ν)))
      (swap* ε φ (γ ** (ψ ** f ν)))
      (congP (λ _ μ → ε ** (φ ** μ)) (swap* ψ γ (f ν)))
      (congP (λ _ μ → φ ** (ε ** μ)) (swap* ψ γ (f ν)))
      i j
  f (hexagon ε φ ψ ν i j) =
    isSet→SquareP (λ i j → trunc* (hexagon ε φ ψ ν i j))
      (doubleCompPathP {B = B}
        (swap* ε φ (ψ ** f ν))
        (congP (λ _ → φ **_) (swap* ε ψ (f ν)))
        (swap* φ ψ (ε ** f ν)))
      (doubleCompPathP {B = B}
        (congP (λ _ → ε **_) (swap* φ ψ (f ν)))
        (swap* ε ψ (φ ** f ν))
        (congP (λ _ → ψ **_) (swap* ε φ (f ν))))
      refl
      refl
      i j
  f (trunc ν μ p q P Q i j k) =
    isOfHLevel→isOfHLevelDep 3 (λ ν → isSet→isGroupoid (trunc* ν))
      (f ν) (f μ)
      (λ i → f (p i)) (λ i → f (q i))
      (λ i j → f (P i j)) (λ i j → f (Q i j))
      (trunc ν μ p q P Q)
      i j k


module ElimPropNF {n ℓ} {B : NF n → Type ℓ} (trunc* : ∀ ν → isProp (B ν))
  (⊤* : B ⊤)
  (_**_ : ∀ φ {ν} (ν* : B ν) → B (φ *ᶠ ν))
  where

  f : ∀ ν → B ν
  f = ElimSetNF.f (λ ν → isProp→isSet (trunc* ν)) ⊤* _**_
    (λ φ ψ {ν} ν* →
      isProp→PathP
        (λ i → trunc* (swap φ ψ ν i))
        (φ ** (ψ ** ν*))
        (ψ ** (φ ** ν*)))

--------------------------------------------------------------------------------

*-identityˡ : (ν : NF n) → ⊤ * ν ≡ ν
*-identityˡ _ = refl

*-identityʳ : (ν : NF n) → ν * ⊤ ≡ ν
*-identityʳ =
  ElimSetNF.f
    (λ ν → trunc (ν * ⊤) ν)
    refl
    (λ φ → cong (φ *ᶠ_))
    (λ φ ψ ih j i → swap φ ψ (ih i) j)

*-assoc : (ν μ ι : NF n) → (ν * μ) * ι ≡ ν * (μ * ι)
*-assoc =
  ElimSetNF.f
    (λ ν → isSetΠ2 λ μ ι → trunc ((ν * μ) * ι) (ν * (μ * ι)))
    (λ _ _ → refl)
    (λ φ ih μ ι → cong (φ *ᶠ_) (ih μ ι))
    (λ φ ψ ih j μ ι i → swap φ ψ (ih μ ι i) j)
