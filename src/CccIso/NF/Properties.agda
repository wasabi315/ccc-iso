module CccIso.NF.Properties where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.GroupoidLaws using (cong-∙)
open import Cubical.Foundations.HLevels using
  ( isOfHLevel→isOfHLevelDep; isSet→isGroupoid; isSet→SquareP
  ; isSetΠ; isPropΠ3; isSetΠ2; isSetΣ; isOfHLevelPathP; isOfHLevelPathP')
open import Cubical.Data.Fin.Recursive.Base using (Fin)
open import Cubical.Data.Nat.Base using (ℕ)
open import Cubical.Data.Sigma using (Σ-syntax; _,_; fst; snd; ΣPathPProp)

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
-- Some basic properties

-- swap is natural
swap-natural : (φ ψ : Factor n) (ν μ : NF n) (p : ν ≡ μ) →
  Square
    (swap φ ψ ν)
    (swap φ ψ μ)
    (cong (λ ι → φ *ᶠ ψ *ᶠ ι) p)
    (cong (λ ι → ψ *ᶠ φ *ᶠ ι) p)
swap-natural φ ψ ν μ =
  J (λ ι p →
      Square
        (swap φ ψ ν)
        (swap φ ψ ι)
        (cong (λ ζ → φ *ᶠ ψ *ᶠ ζ) p)
        (cong (λ ζ → ψ *ᶠ φ *ᶠ ζ) p))
    refl

-- two independent swaps happen away from each other commute
swap-commute : (ε φ ψ γ : Factor n) (ν μ : NF n) →
  Square
    (swap ε φ (ν * ψ *ᶠ γ *ᶠ μ))
    (swap ε φ (ν * γ *ᶠ ψ *ᶠ μ))
    (cong (λ ι → ε *ᶠ φ *ᶠ ν * ι) (swap ψ γ μ))
    (cong (λ ι → φ *ᶠ ε *ᶠ ν * ι) (swap ψ γ μ))
swap-commute ε φ ψ γ ν μ =
  swap-natural ε φ (ν * ψ *ᶠ γ *ᶠ μ) (ν * γ *ᶠ ψ *ᶠ μ) (cong (ν *_) (swap ψ γ μ))

swap-sym : (φ ψ : Factor n) (ν : NF n) → swap φ ψ ν ≡ sym (swap ψ φ ν)
swap-sym φ ψ ν j i =
  hcomp
    (λ where
      k (i = i0) → swap ψ φ ν (~ j ∨ k)
      k (i = i1) → ψ *ᶠ φ *ᶠ ν
      k (j = i0) → swap φ ψ ν i
      k (j = i1) → swap ψ φ ν (~ i ∧ k))
    (invol φ ψ ν j i)

--------------------------------------------------------------------------------
-- Important property

-- Bring one factor in the middle to the front.
-- This can be done in a way that commutes with swaps happening for previous factors.
shift : (φ : Factor n) (ν μ : NF n) → ν * φ *ᶠ μ ≡ φ *ᶠ ν * μ
shift φ =
  ElimSetNF.f
    (λ ν → isSetΠ λ μ → trunc (ν * φ *ᶠ μ) (φ *ᶠ ν * μ))
    (λ _ → refl)
    (λ ψ {ν} ih μ → step ψ ν μ (ih μ))
    (λ ε ψ {ν} ih → funExt λ μ → step-swap ε ψ ν μ (ih μ))
  where
    step : ∀ ψ ν μ
      → ν * φ *ᶠ μ ≡ φ *ᶠ ν * μ
      → ψ *ᶠ ν * φ *ᶠ μ ≡ φ *ᶠ ψ *ᶠ ν * μ
    step ψ ν μ p = cong (ψ *ᶠ_) p ∙ swap ψ φ (ν * μ)

    step-swap : ∀ ε ψ ν μ (p : ν * φ *ᶠ μ ≡ φ *ᶠ ν * μ) →
      Square
        (step ε (ψ *ᶠ ν) μ (step ψ ν μ p))
        (step ψ (ε *ᶠ ν) μ (step ε ν μ p))
        (swap ε ψ (ν * φ *ᶠ μ))
        (cong (φ *ᶠ_) (swap ε ψ (ν * μ)))
    step-swap ε ψ ν μ p = square9
      where
        square0 : Square
          (cong (λ ι → ε *ᶠ ψ *ᶠ ι) p)
          (cong (λ ι → ψ *ᶠ ε *ᶠ ι) p)
          (swap ε ψ (ν * φ *ᶠ μ))
          (swap ε ψ (φ *ᶠ ν * μ))
        square0 j i = swap-natural ε ψ (ν * φ *ᶠ μ) (φ *ᶠ ν * μ) p i j

        square1 : Square
          (sym (cong (ε *ᶠ_) (swap φ ψ (ν * μ))))
          (cong (ψ *ᶠ_) (swap ε φ (ν * μ)))
          (swap ε ψ (φ *ᶠ ν * μ))
          (cong (ε *ᶠ_) (swap φ ψ (ν * μ))
            ∙∙ swap ε ψ (φ *ᶠ ν * μ)
            ∙∙ cong (ψ *ᶠ_) (swap ε φ (ν * μ)))
        square1 j i =
          doubleCompPath-filler
            (cong (ε *ᶠ_) (swap φ ψ (ν * μ)))
            (swap ε ψ (φ *ᶠ ν * μ))
            (cong (ψ *ᶠ_) (swap ε φ (ν * μ)))
            i j

        square2 : Square
          (cong (ε *ᶠ_) (swap ψ φ (ν * μ)))
          (sym (cong (ε *ᶠ_) (swap φ ψ (ν * μ))))
          refl
          refl
        square2 = cong (cong (ε *ᶠ_)) (swap-sym ψ φ (ν * μ))

        square3 : Square
          (cong (ε *ᶠ_) (swap ψ φ (ν * μ)))
          (cong (ψ *ᶠ_) (swap ε φ (ν * μ)))
          (swap ε ψ (φ *ᶠ ν * μ))
          (cong (ε *ᶠ_) (swap φ ψ (ν * μ))
            ∙∙ swap ε ψ (φ *ᶠ ν * μ)
            ∙∙ cong (ψ *ᶠ_) (swap ε φ (ν * μ)))
        square3 = square2 ◁ square1

        square4 : Square
          (cong (ε *ᶠ_) (cong (ψ *ᶠ_) p ∙ swap ψ φ (ν * μ)))
          (cong (ψ *ᶠ_) (cong (ε *ᶠ_) p ∙ swap ε φ (ν * μ)))
          (swap ε ψ (ν * φ *ᶠ μ))
          (cong (ε *ᶠ_) (swap φ ψ (ν * μ))
            ∙∙ swap ε ψ (φ *ᶠ ν * μ)
            ∙∙ cong (ψ *ᶠ_) (swap ε φ (ν * μ)))
        square4 =
          cong-∙ (ε *ᶠ_) _ _ ◁ square0 ∙₂ square3 ▷ sym (cong-∙ (ψ *ᶠ_) _ _)

        square5 : Square
          (swap ε φ (ψ *ᶠ ν * μ))
          (sym (swap φ ψ (ε *ᶠ ν * μ)))
          (swap ε φ (ψ *ᶠ ν * μ)
            ∙∙ cong (φ *ᶠ_) (swap ε ψ (ν * μ))
            ∙∙ swap φ ψ (ε *ᶠ ν * μ))
          (cong (φ *ᶠ_) (swap ε ψ (ν * μ)))
        square5 j i =
          doubleCompPath-filler
            (swap ε φ (ψ *ᶠ ν * μ))
            (cong (φ *ᶠ_) (swap ε ψ (ν * μ)))
            (swap φ ψ (ε *ᶠ ν * μ))
            (~ i) j

        square6 : Square
          (sym (swap φ ψ (ε *ᶠ ν * μ)))
          (swap ψ φ (ε *ᶠ ν * μ))
          refl
          refl
        square6 = sym (swap-sym ψ φ (ε *ᶠ ν * μ))

        square7 : Square
          (swap ε φ (ψ *ᶠ ν * μ))
          (swap ψ φ (ε *ᶠ ν * μ))
          (swap ε φ (ψ *ᶠ ν * μ)
            ∙∙ cong (φ *ᶠ_) (swap ε ψ (ν * μ))
            ∙∙ swap φ ψ (ε *ᶠ ν * μ))
          (cong (φ *ᶠ_) (swap ε ψ (ν * μ)))
        square7 = square5 ▷ square6

        square8 : Square
          (swap ε φ (ψ *ᶠ ν * μ))
          (swap ψ φ (ε *ᶠ ν * μ))
          (cong (ε *ᶠ_) (swap φ ψ (ν * μ))
            ∙∙ swap ε ψ (φ *ᶠ ν * μ)
            ∙∙ cong (ψ *ᶠ_) (swap ε φ (ν * μ)))
          (cong (φ *ᶠ_) (swap ε ψ (ν * μ)))
        square8 j i =
          hcomp
            (λ where
              k (i = i0) →
                (cong (ε *ᶠ_) (swap φ ψ (ν * μ))
                  ∙∙ swap ε ψ (φ *ᶠ ν * μ)
                  ∙∙ cong (ψ *ᶠ_) (swap ε φ (ν * μ)))
                j
              k (i = i1) → square7 j k
              k (j = i0) → swap ε φ (ψ *ᶠ ν * μ) (i ∧ k)
              k (j = i1) → swap ψ φ (ε *ᶠ ν * μ) (i ∧ k))
            (hexagon ε φ ψ (ν * μ) (~ i) j)

        square9 : Square
          (cong (ε *ᶠ_) (cong (ψ *ᶠ_) p ∙ swap ψ φ (ν * μ))
            ∙ swap ε φ (ψ *ᶠ ν * μ))
          (cong (ψ *ᶠ_) (cong (ε *ᶠ_) p ∙ swap ε φ (ν * μ))
            ∙ swap ψ φ (ε *ᶠ ν * μ))
          (swap ε ψ (ν * φ *ᶠ μ))
          (cong (φ *ᶠ_) (swap ε ψ (ν * μ)))
        square9 = square4 ∙₂ square8

long-swap : (φ ψ : Factor n) (ν μ : NF n) → φ *ᶠ ν * ψ *ᶠ μ ≡ ψ *ᶠ ν * φ *ᶠ μ
long-swap φ ψ ν μ = shift ψ (φ *ᶠ ν) μ ∙ cong (ψ *ᶠ_) (sym (shift φ ν μ))

--------------------------------------------------------------------------------
-- Properties of product and exponential

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

⇒ᶠ-curry : (ν μ : NF n) (φ : Factor n) → ν ⇒ᶠ (μ ⇒ᶠ φ) ≡ (ν * μ) ⇒ᶠ φ
⇒ᶠ-curry ν μ (ι ⇒ᵃ α) = cong (_⇒ᵃ α) (sym (*-assoc ν μ ι))

⇒-curry : (ν μ ι : NF n) → ν ⇒ (μ ⇒ ι) ≡ (ν * μ) ⇒ ι
⇒-curry ν μ =
  ElimSetNF.f
    (λ ι → trunc (ν ⇒ (μ ⇒ ι)) ((ν * μ) ⇒ ι))
    refl
    (λ φ ih → cong₂ _*ᶠ_ (⇒ᶠ-curry ν μ φ) ih)
    (λ φ ψ ih j i → swap (⇒ᶠ-curry ν μ φ i) (⇒ᶠ-curry ν μ ψ i) (ih i) j)

⇒-distribˡ : (ν μ ι : NF n) → ν ⇒ (μ * ι) ≡ (ν ⇒ μ) * (ν ⇒ ι)
⇒-distribˡ ν =
  ElimSetNF.f
    (λ μ → isSetΠ λ ι → trunc (ν ⇒ (μ * ι)) ((ν ⇒ μ) * (ν ⇒ ι)))
    (λ _ → refl)
    (λ φ ih ι → cong ((ν ⇒ᶠ φ) *ᶠ_) (ih ι))
    (λ φ ψ ih j ι i → swap (ν ⇒ᶠ φ) (ν ⇒ᶠ ψ) (ih ι i) j)

⇒ᶠ-identityˡ : (φ : Factor n) → ⊤ ⇒ᶠ φ ≡ φ
⇒ᶠ-identityˡ (ν ⇒ᵃ α) = refl

⇒-identityˡ : (ν : NF n) → ⊤ ⇒ ν ≡ ν
⇒-identityˡ =
  ElimSetNF.f
    (λ ν → trunc (⊤ ⇒ ν) ν)
    refl
    (λ φ ih → cong₂ _*ᶠ_ (⇒ᶠ-identityˡ φ) ih)
    (λ φ ψ ih j i → swap (⇒ᶠ-identityˡ φ i) (⇒ᶠ-identityˡ ψ i) (ih i) j)

⇒-annihilʳ : (ν : NF n) → ν ⇒ ⊤ ≡ ⊤
⇒-annihilʳ _ = refl
