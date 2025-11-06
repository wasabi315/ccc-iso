module CccIso.NF.Properties where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels using
  ( isOfHLevel→isOfHLevelDep; isSet→isGroupoid; isSet→SquareP
  ; isSetΠ; isPropΠ2; isSetΠ2; isSetΣ; isOfHLevelPathP; isOfHLevelPathP')
open import Cubical.Foundations.GroupoidLaws using (cong-∙)
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
-- Some basic properties

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

--------------------------------------------------------------------------------
-- Important properties

module Shift (φ : Factor n) where

  -- Pull one factor in the middle to the front.
  -- This can be done in a way that commutes with swaps happening for previous elements.

  Line : ∀ ν μ → Type
  Line ν μ = ν * φ *ᶠ μ ≡ φ *ᶠ ν * μ

  Comm : ∀ ν μ (line : Line ν μ) → Type
  Comm ν μ line =
    ∀ ε ψ →
      Square
        (swap ε ψ (ν * φ *ᶠ μ))
        (swap ε ψ (φ *ᶠ ν * μ))
        (cong (λ μ → ε *ᶠ ψ *ᶠ μ) line)
        (cong (λ μ → ψ *ᶠ ε *ᶠ μ) line)

  Motive : ∀ ν μ → Type
  Motive ν μ = Σ[ line ∈ Line ν μ ] Comm ν μ line

  isSetLine : ∀ ν μ → isSet (Line ν μ)
  isSetLine ν μ = trunc (ν * φ *ᶠ μ) (φ *ᶠ ν * μ)

  isPropComm : ∀ ν μ (line : Line ν μ) → isProp (Comm ν μ line)
  isPropComm ν μ p =
    isPropΠ2 λ ε ψ →
      isOfHLevelPathP' 1
        (trunc (ε *ᶠ ψ *ᶠ φ *ᶠ ν * μ) (ψ *ᶠ ε *ᶠ φ *ᶠ ν * μ))
        (swap ε ψ (ν * φ *ᶠ μ))
        (swap ε ψ (φ *ᶠ ν * μ))

  isSetMotive : ∀ ν μ → isSet (Motive ν μ)
  isSetMotive ν μ =
    isSetΣ (isSetLine ν μ) λ line → isProp→isSet (isPropComm ν μ line)

  base : ∀ ν → Motive ⊤ ν
  base ν = refl , λ _ _ → refl

  step-line : ∀ ψ ν μ → Line ν μ → Line (ψ *ᶠ ν) μ
  step-line ψ ν μ line = cong (ψ *ᶠ_) line ∙ swap ψ φ (ν * μ)

  step-comm : ∀ ψ ν μ (line : Line ν μ)
    → Comm ν μ line
    → Comm (ψ *ᶠ ν) μ (step-line ψ ν μ line)
  step-comm ψ ν μ line comm = {!   !}

  step : ∀ ψ ν μ → Motive ν μ → Motive (ψ *ᶠ ν) μ
  step ψ ν μ (line , comm) =
    step-line ψ ν μ line , step-comm ψ ν μ line comm

  step-swap : ∀ ε ψ ν μ (motive : Motive ν μ) →
    PathP (λ i → Motive (swap ε ψ ν i) μ)
      (step ε (ψ *ᶠ ν) μ (step ψ ν μ motive))
      (step ψ (ε *ᶠ ν) μ (step ε ν μ motive))
  step-swap ε ψ ν μ (line , comm) =
    ΣPathPProp (isPropComm (ψ *ᶠ ε *ᶠ ν) μ) square9
    where
      square0 : Square
        (cong (λ ι → ε *ᶠ ψ *ᶠ ι) line)
        (cong (λ ι → ψ *ᶠ ε *ᶠ ι) line)
        (swap ε ψ (ν * φ *ᶠ μ))
        (swap ε ψ (φ *ᶠ ν * μ))
      square0 j i = comm ε ψ i j

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
      square2 = cong (cong (ε *ᶠ_)) (invol'' ψ φ (ν * μ))

      square3 : Square
        (cong (ε *ᶠ_) (swap ψ φ (ν * μ)))
        (cong (ψ *ᶠ_) (swap ε φ (ν * μ)))
        (swap ε ψ (φ *ᶠ ν * μ))
        (cong (ε *ᶠ_) (swap φ ψ (ν * μ))
          ∙∙ swap ε ψ (φ *ᶠ ν * μ)
          ∙∙ cong (ψ *ᶠ_) (swap ε φ (ν * μ)))
      square3 = square2 ◁ square1

      square4 : Square
        (cong (ε *ᶠ_) (cong (ψ *ᶠ_) line ∙ swap ψ φ (ν * μ)))
        (cong (ψ *ᶠ_) (cong (ε *ᶠ_) line ∙ swap ε φ (ν * μ)))
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
      square6 = sym (invol'' ψ φ (ε *ᶠ ν * μ))

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
        (cong (ε *ᶠ_) (cong (ψ *ᶠ_) line ∙ swap ψ φ (ν * μ))
          ∙ swap ε φ (ψ *ᶠ ν * μ))
        (cong (ψ *ᶠ_) (cong (ε *ᶠ_) line ∙ swap ε φ (ν * μ))
          ∙ swap ψ φ (ε *ᶠ ν * μ))
        (swap ε ψ (ν * φ *ᶠ μ))
        (cong (φ *ᶠ_) (swap ε ψ (ν * μ)))
      square9 = square4 ∙₂ square8

  f : ∀ ν μ → Motive ν μ
  f =
    ElimSetNF.f
      (λ ν → isSetΠ λ μ → isSetMotive ν μ)
      base
      (λ ψ {ν} ih μ → step ψ ν μ (ih μ))
      (λ ε ψ {ν} ih → funExt λ μ → step-swap ε ψ ν μ (ih μ))

  shift : (ν μ : NF n) → ν * φ *ᶠ μ ≡ φ *ᶠ ν * μ
  shift ν μ = f ν μ .fst

  shift-square : (ε ψ : Factor n) (ν μ : NF n)
    → Square
        (swap ε ψ (ν * φ *ᶠ μ))
        (swap ε ψ (φ *ᶠ ν * μ))
        (cong (λ ι → ε *ᶠ ψ *ᶠ ι) (shift ν μ))
        (cong (λ ι → ψ *ᶠ ε *ᶠ ι) (shift ν μ))
  shift-square ε ψ ν μ = f ν μ .snd ε ψ

open Shift using (shift; shift-square) public
