module CccIso.NF.Properties where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.GroupoidLaws using
  ( cong-∙; cong-∙∙; doubleCompPath-elim; doubleCompPath-elim'
  ; assoc; rUnit; lUnit)
open import Cubical.Foundations.HLevels using
  ( isOfHLevel→isOfHLevelDep; isSet→isGroupoid; isSet→SquareP
  ; isPropΠ; isPropΠ3; isSetΠ; isSetΠ2)
open import Cubical.Foundations.Path using (flipSquare; compPath→Square; Square→compPath; _∙v_)
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
-- Utils

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

doubleCompPaths→Square : ∀ {a} {A : Type a} {x y y' z z' w : A} →
  {p : x ≡ y} {q : y ≡ z} {r : z ≡ w} →
  {p' : x ≡ y'} {q' : y' ≡ z'} {r' : z' ≡ w} →
  (p ∙∙ q ∙∙ r) ≡ (p' ∙∙ q' ∙∙ r') →
  Square (p ∙ q) (q' ∙ r') p' r
doubleCompPaths→Square P =
  compPath→Square
    (sym (doubleCompPath-elim' _ _ _) ∙∙ sym P ∙∙ doubleCompPath-elim _ _ _)

doubleCompPaths→Square' : ∀ {a} {A : Type a} {x y y' z z' w : A} →
  {p : x ≡ y} {q : y ≡ z} {r : z ≡ w} →
  {p' : x ≡ y'} {q' : y' ≡ z'} {r' : z' ≡ w} →
  (p ∙∙ q ∙∙ r) ≡ (p' ∙∙ q' ∙∙ r') →
  Square p r' (p' ∙ q') (q ∙ r)
doubleCompPaths→Square' P =
  compPath→Square
    (sym (doubleCompPath-elim _ _ _) ∙∙ sym P ∙∙ doubleCompPath-elim' _ _ _)

Square→doubleCompPath' : ∀ {a} {A : Type a} {x y y' z z' w : A} →
  {p : x ≡ y} {q : y ≡ z} {r : z ≡ w} →
  {p' : x ≡ y'} {q' : y' ≡ z'} {r' : z' ≡ w} →
  Square p r' (p' ∙ q') (q ∙ r) →
  (p ∙∙ q ∙∙ r) ≡ (p' ∙∙ q' ∙∙ r')
Square→doubleCompPath' P =
  doubleCompPath-elim' _ _ _
    ∙∙ sym (Square→compPath P)
    ∙∙ sym (doubleCompPath-elim _ _ _)

doubleRUnit : ∀ {a} {A : Type a} {x y : A} (p : x ≡ y) → p ≡ (p ∙∙ refl ∙∙ refl)
doubleRUnit p = rUnit _ ∙∙ rUnit _ ∙∙ sym (doubleCompPath-elim _ _ _)

doubleLUnit : ∀ {a} {A : Type a} {x y : A} (p : x ≡ y) → p ≡ (refl ∙∙ refl ∙∙ p)
doubleLUnit p =
  lUnit _ ∙∙ cong (refl ∙_) (lUnit _) ∙∙ sym (doubleCompPath-elim' _ _ _)

_◁v_▷_ : ∀ {a} {A : Type a} {x y y' z : A} →
  {p : x ≡ y} {p' p'' : x ≡ y'} {q q' : y ≡ z} {q'' : y' ≡ z} →
  (Q : p' ≡ p'') (P : Square p q'' p' q) (R : q ≡ q') →
  Square p q'' p'' q'
Q ◁v P ▷ R = subst2 (Square _ _) Q R P

--------------------------------------------------------------------------------
-- Eliminators

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
      (symP (swap* ψ φ (f ν)))
      refl
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
swap-natural : (φ ψ : Factor n) {ν μ : NF n} (p : ν ≡ μ) →
  Square
    (swap φ ψ ν)
    (swap φ ψ μ)
    (cong (λ ι → φ *ᶠ ψ *ᶠ ι) p)
    (cong (λ ι → ψ *ᶠ φ *ᶠ ι) p)
swap-natural φ ψ =
  J (λ ι p →
      Square
        (swap φ ψ _)
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
  swap-natural ε φ (cong (ν *_) (swap ψ γ μ))

--------------------------------------------------------------------------------
-- Important properties

-- Bring one factor at the front to the middle.
shift : (φ : Factor n) (ν μ : NF n) → φ *ᶠ ν * μ ≡ ν * φ *ᶠ μ
shift φ =
  ElimSetNF.f
    (λ _ → isSetΠ λ _ → trunc _ _)
    (λ _ → refl)
    (λ ψ {ν} ih μ → swap φ ψ (ν * μ) ∙ cong (ψ *ᶠ_) (ih μ))
    (λ ε ψ {ν} ih i μ → shift-swap ε ψ ν μ (ih μ) i)
  where abstract -- abstract greatly improves type checking performance
    shift-swap : ∀ ε ψ ν μ (p : φ *ᶠ ν * μ ≡ ν * φ *ᶠ μ) → Square
      (swap φ ε (ψ *ᶠ ν * μ)
        ∙ cong (ε *ᶠ_) (swap φ ψ (ν * μ) ∙ cong (ψ *ᶠ_) p))
      (swap φ ψ (ε *ᶠ ν * μ)
        ∙ cong (ψ *ᶠ_) (swap φ ε (ν * μ) ∙ cong (ε *ᶠ_) p))
      (cong (φ *ᶠ_) (swap ε ψ (ν * μ)))
      (swap ε ψ (ν * φ *ᶠ μ))
    shift-swap ε ψ ν μ p = square3
      where
        square0 : Square
          (swap φ ε (ψ *ᶠ ν * μ) ∙ cong (ε *ᶠ_) (swap φ ψ (ν * μ)))
          (swap φ ψ (ε *ᶠ ν * μ) ∙ cong (ψ *ᶠ_) (swap φ ε (ν * μ)))
          (cong (φ *ᶠ_) (swap ε ψ (ν * μ)))
          (swap ε ψ (φ *ᶠ ν * μ))
        square0 = doubleCompPaths→Square (hexagon φ ε ψ (ν * μ))

        square1 : Square
          (cong (λ ι → ε *ᶠ ψ *ᶠ ι) p)
          (cong (λ ι → ψ *ᶠ ε *ᶠ ι) p)
          (swap ε ψ (φ *ᶠ ν * μ))
          (swap ε ψ (ν * φ *ᶠ μ))
        square1 = flipSquare (swap-natural ε ψ p)

        square2 : Square
          ((swap φ ε (ψ *ᶠ ν * μ) ∙ cong (ε *ᶠ_) (swap φ ψ (ν * μ)))
            ∙ cong (λ ι → ε *ᶠ ψ *ᶠ ι) p)
          ((swap φ ψ (ε *ᶠ ν * μ) ∙ cong (ψ *ᶠ_) (swap φ ε (ν * μ)))
            ∙ cong (λ ι → ψ *ᶠ ε *ᶠ ι) p)
          (cong (φ *ᶠ_) (swap ε ψ (ν * μ)))
          (swap ε ψ (ν * φ *ᶠ μ))
        square2 = square0 ∙₂ square1

        square3 : Square
          (swap φ ε (ψ *ᶠ ν * μ)
            ∙ cong (ε *ᶠ_) (swap φ ψ (ν * μ) ∙ cong (ψ *ᶠ_) p))
          (swap φ ψ (ε *ᶠ ν * μ)
            ∙ cong (ψ *ᶠ_) (swap φ ε (ν * μ) ∙ cong (ε *ᶠ_) p))
          (cong (φ *ᶠ_) (swap ε ψ (ν * μ)))
          (swap ε ψ (ν * φ *ᶠ μ))
        square3 =
          (cong (swap φ ε _ ∙_) (cong-∙ (ε *ᶠ_) _ _) ∙ assoc _ _ _)
          ◁ square2 ▷
          sym (cong (swap φ ψ _ ∙_) (cong-∙ (ψ *ᶠ_) _ _) ∙ assoc _ _ _)

shift-hexagon : (φ ψ : Factor n) (ν μ : NF n) →
  Path (φ *ᶠ ψ *ᶠ ν * μ ≡ ν * ψ *ᶠ φ *ᶠ μ)
    (swap φ ψ (ν * μ) ∙∙ cong (ψ *ᶠ_) (shift φ ν μ) ∙∙ shift ψ ν (φ *ᶠ μ))
    (cong (φ *ᶠ_) (shift ψ ν μ) ∙∙ shift φ ν (ψ *ᶠ μ) ∙∙ cong (ν *_) (swap φ ψ μ))
shift-hexagon φ ψ =
  ElimPropNF.f
    (λ _ → isPropΠ λ _ → trunc _ _ _ _)
    (λ μ → sym (doubleRUnit (swap φ ψ μ)) ∙ doubleLUnit (swap φ ψ μ))
    (λ ε {ν} ih μ →
      let square0 : Square
            (swap φ ψ (ε *ᶠ ν * μ))
            (cong (ε *ᶠ_) (swap φ ψ (ν * μ)))
            (cong (φ *ᶠ_) (swap ψ ε (ν * μ)) ∙ swap φ ε (ψ *ᶠ ν * μ))
            (cong (ψ *ᶠ_) (swap φ ε (ν * μ)) ∙ swap ψ ε (φ *ᶠ ν * μ))
          square0 = doubleCompPaths→Square' (hexagon φ ψ ε (ν * μ))

          square1 : Square
            (cong (ε *ᶠ_) (swap φ ψ (ν * μ)))
            (cong (λ ι → ε *ᶠ ν * ι) (swap φ ψ μ))
            (cong (λ ι → ε *ᶠ φ *ᶠ ι) (shift ψ ν μ) ∙ cong (ε *ᶠ_) (shift φ ν (ψ *ᶠ μ)))
            (cong (λ ι → ε *ᶠ ψ *ᶠ ι) (shift φ ν μ) ∙ cong (ε *ᶠ_) (shift ψ ν (φ *ᶠ μ)))
          square1 =
            doubleCompPaths→Square'
              (sym (cong-∙∙ (ε *ᶠ_) _ _ _)
                ∙∙ cong (cong (ε *ᶠ_)) (ih μ)
                ∙∙ cong-∙∙ (ε *ᶠ_) _ _ _)

          square2 : Square
            (swap φ ψ (ε *ᶠ ν * μ))
            (cong (λ ι → ε *ᶠ ν * ι) (swap φ ψ μ))
            ((cong (φ *ᶠ_) (swap ψ ε (ν * μ)) ∙ swap φ ε (ψ *ᶠ ν * μ))
              ∙ cong (λ ι → ε *ᶠ φ *ᶠ ι) (shift ψ ν μ) ∙ cong (ε *ᶠ_) (shift φ ν (ψ *ᶠ μ)))
            ((cong (ψ *ᶠ_) (swap φ ε (ν * μ)) ∙ swap ψ ε (φ *ᶠ ν * μ))
              ∙ cong (λ ι → ε *ᶠ ψ *ᶠ ι) (shift φ ν μ) ∙ cong (ε *ᶠ_) (shift ψ ν (φ *ᶠ μ)))
          square2 = square0 ∙v square1

          square3 : Square
            (swap φ ψ (ε *ᶠ ν * μ))
            (cong (λ ι → ε *ᶠ ν * ι) (swap φ ψ μ))
            (cong (φ *ᶠ_) (swap ψ ε (ν * μ) ∙ cong (ε *ᶠ_) (shift ψ ν μ))
              ∙ swap φ ε (ν * ψ *ᶠ μ) ∙ cong (ε *ᶠ_) (shift φ ν (ψ *ᶠ μ)))
            (cong (ψ *ᶠ_) (swap φ ε (ν * μ) ∙ cong (ε *ᶠ_) (shift φ ν μ))
              ∙ swap ψ ε (ν * φ *ᶠ μ) ∙ cong (ε *ᶠ_) (shift ψ ν (φ *ᶠ μ)))
          square3 =
              ( ((cong (φ *ᶠ_) (swap ψ ε (ν * μ)) ∙ swap φ ε (ψ *ᶠ ν * μ))
                  ∙ cong (λ ι → ε *ᶠ φ *ᶠ ι) (shift ψ ν μ)
                  ∙ cong (ε *ᶠ_) (shift φ ν (ψ *ᶠ μ)))
              ≡⟨ sym (assoc _ _ _) ⟩
                cong (φ *ᶠ_) (swap ψ ε (ν * μ))
                  ∙ swap φ ε (ψ *ᶠ ν * μ)
                  ∙ cong (λ ι → ε *ᶠ φ *ᶠ ι) (shift ψ ν μ)
                  ∙ cong (ε *ᶠ_) (shift φ ν (ψ *ᶠ μ))
              ≡⟨ cong (cong (φ *ᶠ_) (swap ψ ε (ν * μ)) ∙_) (assoc _ _ _) ⟩
                cong (φ *ᶠ_) (swap ψ ε (ν * μ))
                  ∙ (swap φ ε (ψ *ᶠ ν * μ) ∙ cong (λ ι → ε *ᶠ φ *ᶠ ι) (shift ψ ν μ))
                  ∙ cong (ε *ᶠ_) (shift φ ν (ψ *ᶠ μ))
              ≡⟨ cong
                  (λ p →
                    cong (φ *ᶠ_) (swap ψ ε (ν * μ)) ∙
                    p ∙ cong (ε *ᶠ_) (shift φ ν (ψ *ᶠ μ)))
                  (Square→compPath (flipSquare (swap-natural φ ε (shift ψ ν μ))))
              ⟩
                cong (φ *ᶠ_) (swap ψ ε (ν * μ))
                  ∙ (cong (λ ι → φ *ᶠ ε *ᶠ ι) (shift ψ ν μ) ∙ swap φ ε (ν * ψ *ᶠ μ))
                  ∙ cong (ε *ᶠ_) (shift φ ν (ψ *ᶠ μ))
              ≡⟨ cong (cong (φ *ᶠ_) (swap ψ ε (ν * μ)) ∙_) (sym (assoc _ _ _)) ⟩
                cong (φ *ᶠ_) (swap ψ ε (ν * μ))
                  ∙ cong (λ ι → φ *ᶠ ε *ᶠ ι) (shift ψ ν μ)
                  ∙ swap φ ε (ν * ψ *ᶠ μ)
                  ∙ cong (ε *ᶠ_) (shift φ ν (ψ *ᶠ μ))
              ≡⟨ assoc _ _ _ ⟩
                (cong (φ *ᶠ_) (swap ψ ε (ν * μ)) ∙ cong (λ ι → φ *ᶠ ε *ᶠ ι) (shift ψ ν μ))
                  ∙ swap φ ε (ν * ψ *ᶠ μ)
                  ∙ cong (ε *ᶠ_) (shift φ ν (ψ *ᶠ μ))
              ≡⟨ cong
                  (λ p → p ∙ swap φ ε (ν * ψ *ᶠ μ) ∙ cong (ε *ᶠ_) (shift φ ν (ψ *ᶠ μ)))
                  (sym (cong-∙ (φ *ᶠ_) _ _))
              ⟩
                (cong (φ *ᶠ_) (swap ψ ε (ν * μ) ∙ cong (ε *ᶠ_) (shift ψ ν μ))
                  ∙ swap φ ε (ν * ψ *ᶠ μ)
                  ∙ cong (ε *ᶠ_) (shift φ ν (ψ *ᶠ μ)))
              ∎)
            ◁v square2 ▷
              ( ((cong (ψ *ᶠ_) (swap φ ε (ν * μ)) ∙ swap ψ ε (φ *ᶠ ν * μ))
                  ∙ cong (λ ι → ε *ᶠ ψ *ᶠ ι) (shift φ ν μ)
                  ∙ cong (ε *ᶠ_) (shift ψ ν (φ *ᶠ μ)))
              ≡⟨ sym (assoc _ _ _) ⟩
                cong (ψ *ᶠ_) (swap φ ε (ν * μ))
                  ∙ swap ψ ε (φ *ᶠ ν * μ)
                  ∙ cong (λ ι → ε *ᶠ ψ *ᶠ ι) (shift φ ν μ)
                  ∙ cong (ε *ᶠ_) (shift ψ ν (φ *ᶠ μ))
              ≡⟨ cong (cong (ψ *ᶠ_) (swap φ ε (ν * μ)) ∙_) (assoc _ _ _) ⟩
                cong (ψ *ᶠ_) (swap φ ε (ν * μ))
                  ∙ (swap ψ ε (φ *ᶠ ν * μ) ∙ cong (λ ι → ε *ᶠ ψ *ᶠ ι) (shift φ ν μ))
                  ∙ cong (ε *ᶠ_) (shift ψ ν (φ *ᶠ μ))
              ≡⟨ cong
                  (λ p →
                    cong (ψ *ᶠ_) (swap φ ε (ν * μ)) ∙
                    p ∙ cong (ε *ᶠ_) (shift ψ ν (φ *ᶠ μ)))
                  (Square→compPath (flipSquare (swap-natural ψ ε (shift φ ν μ))))
              ⟩
                cong (ψ *ᶠ_) (swap φ ε (ν * μ))
                  ∙ (cong (λ ι → ψ *ᶠ ε *ᶠ ι) (shift φ ν μ) ∙ swap ψ ε (ν * φ *ᶠ μ))
                  ∙ cong (ε *ᶠ_) (shift ψ ν (φ *ᶠ μ))
              ≡⟨ cong (cong (ψ *ᶠ_) (swap φ ε (ν * μ)) ∙_) (sym (assoc _ _ _)) ⟩
                cong (ψ *ᶠ_) (swap φ ε (ν * μ))
                  ∙ cong (λ ι → ψ *ᶠ ε *ᶠ ι) (shift φ ν μ)
                  ∙ swap ψ ε (ν * φ *ᶠ μ)
                  ∙ cong (ε *ᶠ_) (shift ψ ν (φ *ᶠ μ))
              ≡⟨ assoc _ _ _ ⟩
                (cong (ψ *ᶠ_) (swap φ ε (ν * μ)) ∙ cong (λ ι → ψ *ᶠ ε *ᶠ ι) (shift φ ν μ))
                  ∙ swap ψ ε (ν * φ *ᶠ μ)
                  ∙ cong (ε *ᶠ_) (shift ψ ν (φ *ᶠ μ))
              ≡⟨ cong
                  (λ p → p ∙ swap ψ ε (ν * φ *ᶠ μ) ∙ cong (ε *ᶠ_) (shift ψ ν (φ *ᶠ μ)))
                  (sym (cong-∙ (ψ *ᶠ_) _ _))
              ⟩
                (cong (ψ *ᶠ_) (swap φ ε (ν * μ) ∙ cong (ε *ᶠ_) (shift φ ν μ))
                  ∙ swap ψ ε (ν * φ *ᶠ μ)
                  ∙ cong (ε *ᶠ_) (shift ψ ν (φ *ᶠ μ)))
              ∎)
      in Square→doubleCompPath' square3)

--------------------------------------------------------------------------------
-- Properties of product and exponential

*-identityˡ : (ν : NF n) → ⊤ * ν ≡ ν
*-identityˡ _ = refl

*-identityʳ : (ν : NF n) → ν * ⊤ ≡ ν
*-identityʳ =
  ElimSetNF.f
    (λ _ → trunc _ _)
    refl
    (λ φ → cong (φ *ᶠ_))
    (λ φ ψ ih j i → swap φ ψ (ih i) j)

*-comm : (ν μ : NF n) → ν * μ ≡ μ * ν
*-comm =
  ElimSetNF.f
    (λ _ → isSetΠ λ _ → trunc _ _)
    (λ μ → sym (*-identityʳ μ))
    (λ φ {ν} ih μ → cong (φ *ᶠ_) (ih μ) ∙ shift φ μ ν)
    (λ φ ψ {ν} ih → funExt λ μ →
      let square0 : Square
            (cong (λ ι → φ *ᶠ ψ *ᶠ ι) (ih μ))
            (cong (λ ι → ψ *ᶠ φ *ᶠ ι) (ih μ))
            (swap φ ψ (ν * μ))
            (swap φ ψ (μ * ν))
          square0 = flipSquare (swap-natural φ ψ (ih μ))

          square1 : Square
            (cong (φ *ᶠ_) (shift ψ μ ν) ∙ shift φ μ (ψ *ᶠ ν))
            (cong (ψ *ᶠ_) (shift φ μ ν) ∙ shift ψ μ (φ *ᶠ ν))
            (swap φ ψ (μ * ν))
            (cong (μ *_) (swap φ ψ ν))
          square1 = flipSquare (doubleCompPaths→Square' (shift-hexagon φ ψ μ ν))

          square2 : Square
            (cong (λ ι → φ *ᶠ ψ *ᶠ ι) (ih μ)
              ∙ cong (φ *ᶠ_) (shift ψ μ ν)
              ∙ shift φ μ (ψ *ᶠ ν))
            (cong (λ ι → ψ *ᶠ φ *ᶠ ι) (ih μ)
              ∙ cong (ψ *ᶠ_) (shift φ μ ν)
              ∙ shift ψ μ (φ *ᶠ ν))
            (swap φ ψ (ν * μ))
            (cong (μ *_) (swap φ ψ ν))
          square2 = square0 ∙₂ square1

          square3 : Square
            (cong (φ *ᶠ_) (cong (ψ *ᶠ_) (ih μ) ∙ shift ψ μ ν) ∙ shift φ μ (ψ *ᶠ ν))
            (cong (ψ *ᶠ_) (cong (φ *ᶠ_) (ih μ) ∙ shift φ μ ν) ∙ shift ψ μ (φ *ᶠ ν))
            (swap φ ψ (ν * μ))
            (cong (μ *_) (swap φ ψ ν))
          square3 =
            (cong (_∙ shift φ μ _) (cong-∙∙ (φ *ᶠ_) _ _ _) ∙ sym (assoc _ _ _))
            ◁ square2 ▷
            sym (cong (_∙ shift ψ μ _) (cong-∙∙ (ψ *ᶠ_) _ _ _) ∙ sym (assoc _ _ _))
       in square3)

*-assoc : (ν μ ι : NF n) → (ν * μ) * ι ≡ ν * (μ * ι)
*-assoc =
  ElimSetNF.f
    (λ _ → isSetΠ2 λ _ _ → trunc _ _)
    (λ _ _ → refl)
    (λ φ ih μ ι → cong (φ *ᶠ_) (ih μ ι))
    (λ φ ψ ih j μ ι i → swap φ ψ (ih μ ι i) j)

⇒ᶠ-curry : (ν μ : NF n) (φ : Factor n) → ν ⇒ᶠ (μ ⇒ᶠ φ) ≡ (ν * μ) ⇒ᶠ φ
⇒ᶠ-curry ν μ (ι ⇒ᵃ α) = cong (_⇒ᵃ α) (sym (*-assoc ν μ ι))

⇒-curry : (ν μ ι : NF n) → ν ⇒ (μ ⇒ ι) ≡ (ν * μ) ⇒ ι
⇒-curry ν μ =
  ElimSetNF.f
    (λ _ → trunc _ _)
    refl
    (λ φ ih → cong₂ _*ᶠ_ (⇒ᶠ-curry ν μ φ) ih)
    (λ φ ψ ih j i → swap (⇒ᶠ-curry ν μ φ i) (⇒ᶠ-curry ν μ ψ i) (ih i) j)

⇒-distribˡ : (ν μ ι : NF n) → ν ⇒ (μ * ι) ≡ (ν ⇒ μ) * (ν ⇒ ι)
⇒-distribˡ ν =
  ElimSetNF.f
    (λ _ → isSetΠ λ _ → trunc _ _)
    (λ _ → refl)
    (λ φ ih ι → cong ((ν ⇒ᶠ φ) *ᶠ_) (ih ι))
    (λ φ ψ ih j ι i → swap (ν ⇒ᶠ φ) (ν ⇒ᶠ ψ) (ih ι i) j)

⇒ᶠ-identityˡ : (φ : Factor n) → ⊤ ⇒ᶠ φ ≡ φ
⇒ᶠ-identityˡ (ν ⇒ᵃ α) = refl

⇒-identityˡ : (ν : NF n) → ⊤ ⇒ ν ≡ ν
⇒-identityˡ =
  ElimSetNF.f
    (λ _ → trunc _ _)
    refl
    (λ φ ih → cong₂ _*ᶠ_ (⇒ᶠ-identityˡ φ) ih)
    (λ φ ψ ih j i → swap (⇒ᶠ-identityˡ φ i) (⇒ᶠ-identityˡ ψ i) (ih i) j)

⇒-annihilʳ : (ν : NF n) → ν ⇒ ⊤ ≡ ⊤
⇒-annihilʳ _ = refl
