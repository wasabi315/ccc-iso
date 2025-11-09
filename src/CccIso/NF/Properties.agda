module CccIso.NF.Properties where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.GroupoidLaws using
  (cong-∙; cong-∙∙; doubleCompPath-elim; doubleCompPath-elim';
    assoc; rUnit; lUnit)
open import Cubical.Foundations.Path using
  (flipSquare; compPath→Square; Square→compPath; _∙v_)
open import Cubical.Data.Nat.Base using (ℕ)

open import CccIso.NF

private
  variable
    n : ℕ

--------------------------------------------------------------------------------
-- Utilities

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

module ElimSetNF {n ℓ} {B : NF n → Type ℓ} (trunc* : ∀ α → isSet (B α))
  (⊤* : B ⊤)
  (_**_ : ∀ φ {α} (α* : B α) → B (φ *ᶠ α))
  (swap* : ∀ φ ψ {α} (α* : B α) →
    PathP (λ i → B (swap φ ψ α i)) (φ ** (ψ ** α*)) (ψ ** (φ ** α*)))
  where

  f : ∀ α → B α
  f ⊤ = ⊤*
  f (φ *ᶠ α) = φ ** f α
  f (swap φ ψ α i) = swap* φ ψ (f α) i
  f (invol φ ψ α i j) =
    isSet→SquareP (λ i j → trunc* (invol φ ψ α i j))
      (swap* φ ψ (f α))
      (symP (swap* ψ φ (f α)))
      refl
      refl
      i j
  f (hexagon ε φ ψ α i j) =
    isSet→SquareP (λ i j → trunc* (hexagon ε φ ψ α i j))
      (doubleCompPathP {B = B}
        (swap* ε φ (ψ ** f α))
        (congP (λ _ → φ **_) (swap* ε ψ (f α)))
        (swap* φ ψ (ε ** f α)))
      (doubleCompPathP {B = B}
        (congP (λ _ → ε **_) (swap* φ ψ (f α)))
        (swap* ε ψ (φ ** f α))
        (congP (λ _ → ψ **_) (swap* ε φ (f α))))
      refl
      refl
      i j
  f (trunc α β p q P Q i j k) =
    isOfHLevel→isOfHLevelDep 3 (λ α → isSet→isGroupoid (trunc* α))
      (f α) (f β)
      (λ i → f (p i)) (λ i → f (q i))
      (λ i j → f (P i j)) (λ i j → f (Q i j))
      (trunc α β p q P Q)
      i j k


module ElimPropNF {n ℓ} {B : NF n → Type ℓ} (trunc* : ∀ α → isProp (B α))
  (⊤* : B ⊤)
  (_**_ : ∀ φ {α} (α* : B α) → B (φ *ᶠ α))
  where

  f : ∀ α → B α
  f = ElimSetNF.f (λ α → isProp→isSet (trunc* α)) ⊤* _**_
    (λ φ ψ {α} α* →
      isProp→PathP
        (λ i → trunc* (swap φ ψ α i))
        (φ ** (ψ ** α*))
        (ψ ** (φ ** α*)))

--------------------------------------------------------------------------------
-- Some basic properties

-- swap is natural
swap-natural : (φ ψ : Factor n) {α β : NF n} (p : α ≡ β) →
  Square
    (swap φ ψ α)
    (swap φ ψ β)
    (cong (λ γ → φ *ᶠ ψ *ᶠ γ) p)
    (cong (λ γ → ψ *ᶠ φ *ᶠ γ) p)
swap-natural φ ψ =
  J (λ γ p →
      Square
        (swap φ ψ _)
        (swap φ ψ γ)
        (cong (λ ζ → φ *ᶠ ψ *ᶠ ζ) p)
        (cong (λ ζ → ψ *ᶠ φ *ᶠ ζ) p))
    refl

--------------------------------------------------------------------------------
-- Important properties

-- Bring one factor at the front to the middle
shift : (φ : Factor n) (α β : NF n) → φ *ᶠ α * β ≡ α * φ *ᶠ β
shift φ =
  ElimSetNF.f
    (λ _ → isSetΠ λ _ → trunc _ _)
    (λ _ → refl)
    (λ ψ {α} ih β → swap φ ψ (α * β) ∙ cong (ψ *ᶠ_) (ih β))
    (λ ε ψ {α} ih i β → shift-swap ε ψ α β (ih β) i)
  where abstract
    -- abstract greatly improves type checking performance
    -- 7x faster check for *-comm
    shift-swap : ∀ ε ψ α β (p : φ *ᶠ α * β ≡ α * φ *ᶠ β) →
      Square
        (swap φ ε (ψ *ᶠ α * β)
          ∙ cong (ε *ᶠ_) (swap φ ψ (α * β) ∙ cong (ψ *ᶠ_) p))
        (swap φ ψ (ε *ᶠ α * β)
          ∙ cong (ψ *ᶠ_) (swap φ ε (α * β) ∙ cong (ε *ᶠ_) p))
        (cong (φ *ᶠ_) (swap ε ψ (α * β)))
        (swap ε ψ (α * φ *ᶠ β))
    shift-swap ε ψ α β p = square3
      where
        square0 : Square
          (swap φ ε (ψ *ᶠ α * β) ∙ cong (ε *ᶠ_) (swap φ ψ (α * β)))
          (swap φ ψ (ε *ᶠ α * β) ∙ cong (ψ *ᶠ_) (swap φ ε (α * β)))
          (cong (φ *ᶠ_) (swap ε ψ (α * β)))
          (swap ε ψ (φ *ᶠ α * β))
        square0 = doubleCompPaths→Square (hexagon φ ε ψ (α * β))

        square1 : Square
          (cong (λ γ → ε *ᶠ ψ *ᶠ γ) p)
          (cong (λ γ → ψ *ᶠ ε *ᶠ γ) p)
          (swap ε ψ (φ *ᶠ α * β))
          (swap ε ψ (α * φ *ᶠ β))
        square1 = flipSquare (swap-natural ε ψ p)

        square2 : Square
          ((swap φ ε (ψ *ᶠ α * β) ∙ cong (ε *ᶠ_) (swap φ ψ (α * β)))
            ∙ cong (λ γ → ε *ᶠ ψ *ᶠ γ) p)
          ((swap φ ψ (ε *ᶠ α * β) ∙ cong (ψ *ᶠ_) (swap φ ε (α * β)))
            ∙ cong (λ γ → ψ *ᶠ ε *ᶠ γ) p)
          (cong (φ *ᶠ_) (swap ε ψ (α * β)))
          (swap ε ψ (α * φ *ᶠ β))
        square2 = square0 ∙₂ square1

        square3 : Square
          (swap φ ε (ψ *ᶠ α * β)
            ∙ cong (ε *ᶠ_) (swap φ ψ (α * β) ∙ cong (ψ *ᶠ_) p))
          (swap φ ψ (ε *ᶠ α * β)
            ∙ cong (ψ *ᶠ_) (swap φ ε (α * β) ∙ cong (ε *ᶠ_) p))
          (cong (φ *ᶠ_) (swap ε ψ (α * β)))
          (swap ε ψ (α * φ *ᶠ β))
        square3 =
          (cong (swap φ ε _ ∙_) (cong-∙ (ε *ᶠ_) _ _) ∙ assoc _ _ _)
          ◁ square2 ▷
          sym (cong (swap φ ψ _ ∙_) (cong-∙ (ψ *ᶠ_) _ _) ∙ assoc _ _ _)

shift-hexagon : (φ ψ : Factor n) (α β : NF n) →
  Path (φ *ᶠ ψ *ᶠ α * β ≡ α * ψ *ᶠ φ *ᶠ β)
    (swap φ ψ (α * β) ∙∙ cong (ψ *ᶠ_) (shift φ α β) ∙∙ shift ψ α (φ *ᶠ β))
    (cong (φ *ᶠ_) (shift ψ α β) ∙∙ shift φ α (ψ *ᶠ β) ∙∙ cong (α *_) (swap φ ψ β))
shift-hexagon φ ψ =
  ElimPropNF.f
    (λ _ → isPropΠ λ _ → trunc _ _ _ _)
    (λ β → sym (doubleRUnit (swap φ ψ β)) ∙ doubleLUnit (swap φ ψ β))
    (λ ε {α} ih β →
      let square0 : Square
            (swap φ ψ (ε *ᶠ α * β))
            (cong (ε *ᶠ_) (swap φ ψ (α * β)))
            (cong (φ *ᶠ_) (swap ψ ε (α * β)) ∙ swap φ ε (ψ *ᶠ α * β))
            (cong (ψ *ᶠ_) (swap φ ε (α * β)) ∙ swap ψ ε (φ *ᶠ α * β))
          square0 = doubleCompPaths→Square' (hexagon φ ψ ε (α * β))

          square1 : Square
            (cong (ε *ᶠ_) (swap φ ψ (α * β)))
            (cong (λ γ → ε *ᶠ α * γ) (swap φ ψ β))
            (cong (λ γ → ε *ᶠ φ *ᶠ γ) (shift ψ α β) ∙ cong (ε *ᶠ_) (shift φ α (ψ *ᶠ β)))
            (cong (λ γ → ε *ᶠ ψ *ᶠ γ) (shift φ α β) ∙ cong (ε *ᶠ_) (shift ψ α (φ *ᶠ β)))
          square1 =
            doubleCompPaths→Square'
              (sym (cong-∙∙ (ε *ᶠ_) _ _ _)
                ∙∙ cong (cong (ε *ᶠ_)) (ih β)
                ∙∙ cong-∙∙ (ε *ᶠ_) _ _ _)

          square2 : Square
            (swap φ ψ (ε *ᶠ α * β))
            (cong (λ γ → ε *ᶠ α * γ) (swap φ ψ β))
            ((cong (φ *ᶠ_) (swap ψ ε (α * β)) ∙ swap φ ε (ψ *ᶠ α * β))
              ∙ cong (λ γ → ε *ᶠ φ *ᶠ γ) (shift ψ α β) ∙ cong (ε *ᶠ_) (shift φ α (ψ *ᶠ β)))
            ((cong (ψ *ᶠ_) (swap φ ε (α * β)) ∙ swap ψ ε (φ *ᶠ α * β))
              ∙ cong (λ γ → ε *ᶠ ψ *ᶠ γ) (shift φ α β) ∙ cong (ε *ᶠ_) (shift ψ α (φ *ᶠ β)))
          square2 = square0 ∙v square1

          square3 : Square
            (swap φ ψ (ε *ᶠ α * β))
            (cong (λ γ → ε *ᶠ α * γ) (swap φ ψ β))
            (cong (φ *ᶠ_) (swap ψ ε (α * β) ∙ cong (ε *ᶠ_) (shift ψ α β))
              ∙ swap φ ε (α * ψ *ᶠ β) ∙ cong (ε *ᶠ_) (shift φ α (ψ *ᶠ β)))
            (cong (ψ *ᶠ_) (swap φ ε (α * β) ∙ cong (ε *ᶠ_) (shift φ α β))
              ∙ swap ψ ε (α * φ *ᶠ β) ∙ cong (ε *ᶠ_) (shift ψ α (φ *ᶠ β)))
          square3 =
              ( ((cong (φ *ᶠ_) (swap ψ ε (α * β)) ∙ swap φ ε (ψ *ᶠ α * β))
                  ∙ cong (λ γ → ε *ᶠ φ *ᶠ γ) (shift ψ α β)
                  ∙ cong (ε *ᶠ_) (shift φ α (ψ *ᶠ β)))
              ≡⟨ sym (assoc _ _ _) ⟩
                cong (φ *ᶠ_) (swap ψ ε (α * β))
                  ∙ swap φ ε (ψ *ᶠ α * β)
                  ∙ cong (λ γ → ε *ᶠ φ *ᶠ γ) (shift ψ α β)
                  ∙ cong (ε *ᶠ_) (shift φ α (ψ *ᶠ β))
              ≡⟨ cong (cong (φ *ᶠ_) (swap ψ ε (α * β)) ∙_) (assoc _ _ _) ⟩
                cong (φ *ᶠ_) (swap ψ ε (α * β))
                  ∙ (swap φ ε (ψ *ᶠ α * β) ∙ cong (λ γ → ε *ᶠ φ *ᶠ γ) (shift ψ α β))
                  ∙ cong (ε *ᶠ_) (shift φ α (ψ *ᶠ β))
              ≡⟨ cong
                  (λ p →
                    cong (φ *ᶠ_) (swap ψ ε (α * β)) ∙
                    p ∙ cong (ε *ᶠ_) (shift φ α (ψ *ᶠ β)))
                  (Square→compPath (flipSquare (swap-natural φ ε (shift ψ α β))))
              ⟩
                cong (φ *ᶠ_) (swap ψ ε (α * β))
                  ∙ (cong (λ γ → φ *ᶠ ε *ᶠ γ) (shift ψ α β) ∙ swap φ ε (α * ψ *ᶠ β))
                  ∙ cong (ε *ᶠ_) (shift φ α (ψ *ᶠ β))
              ≡⟨ cong (cong (φ *ᶠ_) (swap ψ ε (α * β)) ∙_) (sym (assoc _ _ _)) ⟩
                cong (φ *ᶠ_) (swap ψ ε (α * β))
                  ∙ cong (λ γ → φ *ᶠ ε *ᶠ γ) (shift ψ α β)
                  ∙ swap φ ε (α * ψ *ᶠ β)
                  ∙ cong (ε *ᶠ_) (shift φ α (ψ *ᶠ β))
              ≡⟨ assoc _ _ _ ⟩
                (cong (φ *ᶠ_) (swap ψ ε (α * β)) ∙ cong (λ γ → φ *ᶠ ε *ᶠ γ) (shift ψ α β))
                  ∙ swap φ ε (α * ψ *ᶠ β)
                  ∙ cong (ε *ᶠ_) (shift φ α (ψ *ᶠ β))
              ≡⟨ cong
                  (λ p → p ∙ swap φ ε (α * ψ *ᶠ β) ∙ cong (ε *ᶠ_) (shift φ α (ψ *ᶠ β)))
                  (sym (cong-∙ (φ *ᶠ_) _ _))
              ⟩
                (cong (φ *ᶠ_) (swap ψ ε (α * β) ∙ cong (ε *ᶠ_) (shift ψ α β))
                  ∙ swap φ ε (α * ψ *ᶠ β)
                  ∙ cong (ε *ᶠ_) (shift φ α (ψ *ᶠ β)))
              ∎)
            ◁v square2 ▷
              ( ((cong (ψ *ᶠ_) (swap φ ε (α * β)) ∙ swap ψ ε (φ *ᶠ α * β))
                  ∙ cong (λ γ → ε *ᶠ ψ *ᶠ γ) (shift φ α β)
                  ∙ cong (ε *ᶠ_) (shift ψ α (φ *ᶠ β)))
              ≡⟨ sym (assoc _ _ _) ⟩
                cong (ψ *ᶠ_) (swap φ ε (α * β))
                  ∙ swap ψ ε (φ *ᶠ α * β)
                  ∙ cong (λ γ → ε *ᶠ ψ *ᶠ γ) (shift φ α β)
                  ∙ cong (ε *ᶠ_) (shift ψ α (φ *ᶠ β))
              ≡⟨ cong (cong (ψ *ᶠ_) (swap φ ε (α * β)) ∙_) (assoc _ _ _) ⟩
                cong (ψ *ᶠ_) (swap φ ε (α * β))
                  ∙ (swap ψ ε (φ *ᶠ α * β) ∙ cong (λ γ → ε *ᶠ ψ *ᶠ γ) (shift φ α β))
                  ∙ cong (ε *ᶠ_) (shift ψ α (φ *ᶠ β))
              ≡⟨ cong
                  (λ p →
                    cong (ψ *ᶠ_) (swap φ ε (α * β)) ∙
                    p ∙ cong (ε *ᶠ_) (shift ψ α (φ *ᶠ β)))
                  (Square→compPath (flipSquare (swap-natural ψ ε (shift φ α β))))
              ⟩
                cong (ψ *ᶠ_) (swap φ ε (α * β))
                  ∙ (cong (λ γ → ψ *ᶠ ε *ᶠ γ) (shift φ α β) ∙ swap ψ ε (α * φ *ᶠ β))
                  ∙ cong (ε *ᶠ_) (shift ψ α (φ *ᶠ β))
              ≡⟨ cong (cong (ψ *ᶠ_) (swap φ ε (α * β)) ∙_) (sym (assoc _ _ _)) ⟩
                cong (ψ *ᶠ_) (swap φ ε (α * β))
                  ∙ cong (λ γ → ψ *ᶠ ε *ᶠ γ) (shift φ α β)
                  ∙ swap ψ ε (α * φ *ᶠ β)
                  ∙ cong (ε *ᶠ_) (shift ψ α (φ *ᶠ β))
              ≡⟨ assoc _ _ _ ⟩
                (cong (ψ *ᶠ_) (swap φ ε (α * β)) ∙ cong (λ γ → ψ *ᶠ ε *ᶠ γ) (shift φ α β))
                  ∙ swap ψ ε (α * φ *ᶠ β)
                  ∙ cong (ε *ᶠ_) (shift ψ α (φ *ᶠ β))
              ≡⟨ cong
                  (λ p → p ∙ swap ψ ε (α * φ *ᶠ β) ∙ cong (ε *ᶠ_) (shift ψ α (φ *ᶠ β)))
                  (sym (cong-∙ (ψ *ᶠ_) _ _))
              ⟩
                (cong (ψ *ᶠ_) (swap φ ε (α * β) ∙ cong (ε *ᶠ_) (shift φ α β))
                  ∙ swap ψ ε (α * φ *ᶠ β)
                  ∙ cong (ε *ᶠ_) (shift ψ α (φ *ᶠ β)))
              ∎)
      in Square→doubleCompPath' square3)

--------------------------------------------------------------------------------
-- Properties of product and exponential

*-identityˡ : (α : NF n) → ⊤ * α ≡ α
*-identityˡ _ = refl

*-identityʳ : (α : NF n) → α * ⊤ ≡ α
*-identityʳ =
  ElimSetNF.f
    (λ _ → trunc _ _)
    refl
    (λ φ → cong (φ *ᶠ_))
    (λ φ ψ ih j i → swap φ ψ (ih i) j)

*-comm : (α β : NF n) → α * β ≡ β * α
*-comm =
  ElimSetNF.f
    (λ _ → isSetΠ λ _ → trunc _ _)
    (λ β → sym (*-identityʳ β))
    (λ φ {α} ih β → cong (φ *ᶠ_) (ih β) ∙ shift φ β α)
    (λ φ ψ {α} ih → funExt λ β →
      let square0 : Square
            (cong (λ γ → φ *ᶠ ψ *ᶠ γ) (ih β))
            (cong (λ γ → ψ *ᶠ φ *ᶠ γ) (ih β))
            (swap φ ψ (α * β))
            (swap φ ψ (β * α))
          square0 = flipSquare (swap-natural φ ψ (ih β))

          square1 : Square
            (cong (φ *ᶠ_) (shift ψ β α) ∙ shift φ β (ψ *ᶠ α))
            (cong (ψ *ᶠ_) (shift φ β α) ∙ shift ψ β (φ *ᶠ α))
            (swap φ ψ (β * α))
            (cong (β *_) (swap φ ψ α))
          square1 = flipSquare (doubleCompPaths→Square' (shift-hexagon φ ψ β α))

          square2 : Square
            (cong (λ γ → φ *ᶠ ψ *ᶠ γ) (ih β)
              ∙ cong (φ *ᶠ_) (shift ψ β α)
              ∙ shift φ β (ψ *ᶠ α))
            (cong (λ γ → ψ *ᶠ φ *ᶠ γ) (ih β)
              ∙ cong (ψ *ᶠ_) (shift φ β α)
              ∙ shift ψ β (φ *ᶠ α))
            (swap φ ψ (α * β))
            (cong (β *_) (swap φ ψ α))
          square2 = square0 ∙₂ square1

          square3 : Square
            (cong (φ *ᶠ_) (cong (ψ *ᶠ_) (ih β) ∙ shift ψ β α) ∙ shift φ β (ψ *ᶠ α))
            (cong (ψ *ᶠ_) (cong (φ *ᶠ_) (ih β) ∙ shift φ β α) ∙ shift ψ β (φ *ᶠ α))
            (swap φ ψ (α * β))
            (cong (β *_) (swap φ ψ α))
          square3 =
            (cong (_∙ shift φ β _) (cong-∙∙ (φ *ᶠ_) _ _ _) ∙ sym (assoc _ _ _))
            ◁ square2 ▷
            sym (cong (_∙ shift ψ β _) (cong-∙∙ (ψ *ᶠ_) _ _ _) ∙ sym (assoc _ _ _))
       in square3)

*-assoc : (α β γ : NF n) → (α * β) * γ ≡ α * (β * γ)
*-assoc =
  ElimSetNF.f
    (λ _ → isSetΠ2 λ _ _ → trunc _ _)
    (λ _ _ → refl)
    (λ φ ih β γ → cong (φ *ᶠ_) (ih β γ))
    (λ φ ψ ih j β γ i → swap φ ψ (ih β γ i) j)

⇒ᶠ-curry : (α β : NF n) (φ : Factor n) → α ⇒ᶠ (β ⇒ᶠ φ) ≡ (α * β) ⇒ᶠ φ
⇒ᶠ-curry α β (γ ⇒ι x) = cong (_⇒ι x) (sym (*-assoc α β γ))

⇒-curry : (α β γ : NF n) → α ⇒ (β ⇒ γ) ≡ (α * β) ⇒ γ
⇒-curry α β =
  ElimSetNF.f
    (λ _ → trunc _ _)
    refl
    (λ φ ih → cong₂ _*ᶠ_ (⇒ᶠ-curry α β φ) ih)
    (λ φ ψ ih j i → swap (⇒ᶠ-curry α β φ i) (⇒ᶠ-curry α β ψ i) (ih i) j)

⇒-distribˡ : (α β γ : NF n) → α ⇒ (β * γ) ≡ (α ⇒ β) * (α ⇒ γ)
⇒-distribˡ α =
  ElimSetNF.f
    (λ _ → isSetΠ λ _ → trunc _ _)
    (λ _ → refl)
    (λ φ ih γ → cong ((α ⇒ᶠ φ) *ᶠ_) (ih γ))
    (λ φ ψ ih j γ i → swap (α ⇒ᶠ φ) (α ⇒ᶠ ψ) (ih γ i) j)

⇒ᶠ-identityˡ : (φ : Factor n) → φ ≡ ⊤ ⇒ᶠ φ
⇒ᶠ-identityˡ (α ⇒ι x) = refl

⇒-identityˡ : (α : NF n) → α ≡ ⊤ ⇒ α
⇒-identityˡ =
  ElimSetNF.f
    (λ _ → trunc _ _)
    refl
    (λ φ ih → cong₂ _*ᶠ_ (⇒ᶠ-identityˡ φ) ih)
    (λ φ ψ ih j i → swap (⇒ᶠ-identityˡ φ i) (⇒ᶠ-identityˡ ψ i) (ih i) j)

⇒-annihilʳ : (α : NF n) → α ⇒ ⊤ ≡ ⊤
⇒-annihilʳ _ = refl
