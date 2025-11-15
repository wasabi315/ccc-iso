module CccIso.NF.Properties where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels using
  (isPropΠ; isPropΠ2; isPropΠ3; isSetΠ; isSetΠ2; isOfHLevelPathP')
open import Cubical.Foundations.GroupoidLaws using
  (cong-∙; cong-∙∙; doubleCompPath-elim; doubleCompPath-elim';
    assoc; rUnit; lUnit; symDistr)
open import Cubical.Foundations.Path using
  (flipSquare; compPath→Square; Square→compPath; _∙v_)
open import Cubical.Data.Nat.Base using (ℕ)

open import CccIso.NF

private
  variable
    n : ℕ

--------------------------------------------------------------------------------
-- Utilities

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

_◁v_▷_ : ∀ {a} {A : Type a} {x y y' z : A} →
  {p : x ≡ y} {p' p'' : x ≡ y'} {q q' : y ≡ z} {q'' : y' ≡ z} →
  (Q : p' ≡ p'') (P : Square p q'' p' q) (R : q ≡ q') →
  Square p q'' p'' q'
Q ◁v P ▷ R = subst2 (Square _ _) Q R P

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
  elimSetNF
    (λ _ → isSetΠ λ _ → trunc _ _)
    (λ _ → refl)
    (λ ψ {α} ih β → swap φ ψ (α * β) ∙ cong (ψ *ᶠ_) (ih β))
    (λ ε ψ {α} ih i β → shift-swap ε ψ α β (ih β) i)
  -- Giving an explicit name to the module improves type checking performance for some reason...
  module Shift where abstract
    -- abstract greatly improves type checking performance for *-comm
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
  elimPropNF
    (λ _ → isPropΠ λ _ → trunc _ _ _ _)
    (λ β → sym (doubleRUnit (swap φ ψ β)) ∙ lUnit (swap φ ψ β))
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
  elimSetNF
    (λ _ → trunc _ _)
    refl
    (λ φ → cong (φ *ᶠ_))
    (λ φ ψ ih j i → swap φ ψ (ih i) j)

*-comm : (α β : NF n) → α * β ≡ β * α
*-comm =
  elimSetNF
    (λ _ → isSetΠ λ _ → trunc _ _)
    (λ β → sym (*-identityʳ β))
    (λ φ {α} ih β → cong (φ *ᶠ_) (ih β) ∙ shift φ β α)
    (λ φ ψ {α} ih → funExt λ β → *-comm-swap φ ψ α β (ih β))
  where abstract
    -- this abstract speeds up type checking for *-hexagon and *-bigon
    *-comm-swap : (φ ψ : Factor n) (α β : NF n) (p : α * β ≡ β * α) →
      Square
        (cong (φ *ᶠ_) (cong (ψ *ᶠ_) p ∙ shift ψ β α) ∙ shift φ β (ψ *ᶠ α))
        (cong (ψ *ᶠ_) (cong (φ *ᶠ_) p ∙ shift φ β α) ∙ shift ψ β (φ *ᶠ α))
        (swap φ ψ (α * β))
        (cong (β *_) (swap φ ψ α))
    *-comm-swap φ ψ α β p = square3
      where
        square0 : Square
          (cong (λ γ → φ *ᶠ ψ *ᶠ γ) p)
          (cong (λ γ → ψ *ᶠ φ *ᶠ γ) p)
          (swap φ ψ (α * β))
          (swap φ ψ (β * α))
        square0 = flipSquare (swap-natural φ ψ p)

        square1 : Square
          (cong (φ *ᶠ_) (shift ψ β α) ∙ shift φ β (ψ *ᶠ α))
          (cong (ψ *ᶠ_) (shift φ β α) ∙ shift ψ β (φ *ᶠ α))
          (swap φ ψ (β * α))
          (cong (β *_) (swap φ ψ α))
        square1 = flipSquare (doubleCompPaths→Square' (shift-hexagon φ ψ β α))

        square2 : Square
          (cong (λ γ → φ *ᶠ ψ *ᶠ γ) p
            ∙ cong (φ *ᶠ_) (shift ψ β α)
            ∙ shift φ β (ψ *ᶠ α))
          (cong (λ γ → ψ *ᶠ φ *ᶠ γ) p
            ∙ cong (ψ *ᶠ_) (shift φ β α)
            ∙ shift ψ β (φ *ᶠ α))
          (swap φ ψ (α * β))
          (cong (β *_) (swap φ ψ α))
        square2 = square0 ∙₂ square1

        square3 : Square
          (cong (φ *ᶠ_) (cong (ψ *ᶠ_) p ∙ shift ψ β α) ∙ shift φ β (ψ *ᶠ α))
          (cong (ψ *ᶠ_) (cong (φ *ᶠ_) p ∙ shift φ β α) ∙ shift ψ β (φ *ᶠ α))
          (swap φ ψ (α * β))
          (cong (β *_) (swap φ ψ α))
        square3 =
          (cong (_∙ shift φ β _) (cong-∙∙ (φ *ᶠ_) _ _ _) ∙ sym (assoc _ _ _))
          ◁ square2 ▷
          sym (cong (_∙ shift ψ β _) (cong-∙∙ (ψ *ᶠ_) _ _ _) ∙ sym (assoc _ _ _))

*-assoc : (α β γ : NF n) → (α * β) * γ ≡ α * (β * γ)
*-assoc =
  elimSetNF
    (λ _ → isSetΠ2 λ _ _ → trunc _ _)
    (λ _ _ → refl)
    (λ φ ih β γ → cong (φ *ᶠ_) (ih β γ))
    (λ φ ψ ih j β γ i → swap φ ψ (ih β γ i) j)

⇒ᶠ-curry : (α β : NF n) (φ : Factor n) → α ⇒ᶠ (β ⇒ᶠ φ) ≡ (α * β) ⇒ᶠ φ
⇒ᶠ-curry α β (γ ⇒ι x) = cong (_⇒ι x) (sym (*-assoc α β γ))

⇒-curry : (α β γ : NF n) → α ⇒ (β ⇒ γ) ≡ (α * β) ⇒ γ
⇒-curry α β =
  elimSetNF
    (λ _ → trunc _ _)
    refl
    (λ φ ih → cong₂ _*ᶠ_ (⇒ᶠ-curry α β φ) ih)
    (λ φ ψ ih j i → swap (⇒ᶠ-curry α β φ i) (⇒ᶠ-curry α β ψ i) (ih i) j)

⇒-distribˡ : (α β γ : NF n) → α ⇒ (β * γ) ≡ (α ⇒ β) * (α ⇒ γ)
⇒-distribˡ α =
  elimSetNF
    (λ _ → isSetΠ λ _ → trunc _ _)
    (λ _ → refl)
    (λ φ ih γ → cong ((α ⇒ᶠ φ) *ᶠ_) (ih γ))
    (λ φ ψ ih j γ i → swap (α ⇒ᶠ φ) (α ⇒ᶠ ψ) (ih γ i) j)

⇒ᶠ-identityˡ : (φ : Factor n) → φ ≡ ⊤ ⇒ᶠ φ
⇒ᶠ-identityˡ (α ⇒ι x) = refl

⇒-identityˡ : (α : NF n) → α ≡ ⊤ ⇒ α
⇒-identityˡ =
  elimSetNF
    (λ _ → trunc _ _)
    refl
    (λ φ ih → cong₂ _*ᶠ_ (⇒ᶠ-identityˡ φ) ih)
    (λ φ ψ ih j i → swap (⇒ᶠ-identityˡ φ i) (⇒ᶠ-identityˡ ψ i) (ih i) j)

⇒-annihilʳ : (α : NF n) → α ⇒ ⊤ ≡ ⊤
⇒-annihilʳ _ = refl

*-pentagon : (α β γ δ : NF n) →
  Path (((α * β) * γ) * δ ≡ α * (β * (γ * δ)))
    (*-assoc (α * β) γ δ ∙ *-assoc α β (γ * δ))
    (cong (_* δ) (*-assoc α β γ) ∙∙ *-assoc α (β * γ) δ ∙∙ cong (α *_) (*-assoc β γ δ))
*-pentagon =
  elimPropNF
    (λ _ → isPropΠ3 λ _ _ _ → trunc _ _ _ _)
    (λ β γ δ → sym (rUnit _) ∙ lUnit _)
    (λ φ ih β γ δ →
      sym (cong-∙ (φ *ᶠ_) _ _)
        ∙∙ cong (cong (φ *ᶠ_)) (ih β γ δ)
        ∙∙ cong-∙∙ (φ *ᶠ_) _ _ _)

*-triangle : (α β : NF n) →
  Square
    (*-assoc α ⊤ β)
    (cong (_* β) (*-identityʳ α))
    refl
    (cong (α *_) (*-identityˡ β))
*-triangle =
  elimPropNF
    (λ _ → isPropΠ λ _ → isOfHLevelPathP' 1 (trunc _ _) _ _)
    (λ _ → refl)
    (λ φ ih β → cong (cong (φ *ᶠ_)) (ih β))

*-bigon : (α β : NF n) → *-comm α β ≡ sym (*-comm β α)
*-bigon =
  elimPropNF
    (λ _ → isPropΠ λ _ → trunc _ _ _ _)
    (elimPropNF
      (λ _ → trunc _ _ _ _)
      refl
      (λ ψ ih → cong (cong (ψ *ᶠ_)) ih ∙ rUnit _))
    (λ φ {α} ih →
      elimPropNF
        (λ _ → trunc _ _ _ _)
        (sym (rUnit _) ∙ cong (cong (φ *ᶠ_)) (ih ⊤))
        (λ ψ {β} ih' →
          let square1 : Square
                (cong (φ *ᶠ_) (*-comm α (ψ *ᶠ β)))
                (sym (cong (φ *ᶠ_) (cong (ψ *ᶠ_) (*-comm β α) ∙ shift ψ α β)))
                refl
                refl
              square1 = cong (cong (φ *ᶠ_)) (ih (ψ *ᶠ β))

              square2 : Square
                (sym (cong (φ *ᶠ_) (cong (ψ *ᶠ_) (*-comm β α) ∙ shift ψ α β)))
                (sym (cong (φ *ᶠ_) (shift ψ α β)))
                refl
                (cong (λ γ → φ *ᶠ ψ *ᶠ γ) (*-comm β α))
              square2 =
                congP (λ _ → sym)
                  (cong-∙ (φ *ᶠ_) _ _ ◁ symP (compPath-filler' _ _))

              square3 : Square
                (sym (cong (λ γ → φ *ᶠ ψ *ᶠ γ) (*-comm α β)))
                (cong (λ γ → φ *ᶠ ψ *ᶠ γ) (*-comm β α))
                refl
                refl
              square3 = cong (λ p → sym (cong (λ γ → φ *ᶠ ψ *ᶠ γ) p)) (ih β)

              square4 : Square
                (swap φ ψ (β * α))
                (swap φ ψ (α * β))
                (sym (cong (λ γ → φ *ᶠ ψ *ᶠ γ) (*-comm α β)))
                (sym (cong (λ γ → ψ *ᶠ φ *ᶠ γ) (*-comm α β)))
              square4 = symP (swap-natural φ ψ (*-comm α β))

              square5 : Square
                (swap φ ψ (α * β))
                (sym (swap ψ φ (α * β)))
                refl
                refl
              square5 = invol φ ψ (α * β)

              square6 : Square
                (cong (ψ *ᶠ_) (shift φ β α))
                (cong (ψ *ᶠ_) (cong (φ *ᶠ_) (*-comm α β) ∙ shift φ β α))
                (sym (cong (λ γ → ψ *ᶠ φ *ᶠ γ) (*-comm α β)))
                refl
              square6 = compPath-filler' _ _ ▷ sym (cong-∙ (ψ *ᶠ_) _ _)

              square7 : Square
                (cong (ψ *ᶠ_) (cong (φ *ᶠ_) (*-comm α β) ∙ shift φ β α))
                (sym (cong (ψ *ᶠ_) (*-comm β (φ *ᶠ α))))
                refl
                refl
              square7 = cong (cong (ψ *ᶠ_)) ih'

              square8 : Square
                (sym (cong (φ *ᶠ_) (shift ψ α β))
                    ∙ sym (swap ψ φ (α * β))
                    ∙ sym (cong (ψ *ᶠ_) (*-comm β (φ *ᶠ α))))
                (sym
                    (cong (ψ *ᶠ_) (*-comm β (φ *ᶠ α))
                      ∙ swap ψ φ (α * β)
                      ∙ cong (φ *ᶠ_) (shift ψ α β)))
                refl
                refl
              square8 =
                cong (sym (cong (φ *ᶠ_) (shift ψ α β)) ∙_) (sym (symDistr _ _))
                  ∙∙ sym (symDistr _ _)
                  ∙∙ cong sym (sym (assoc _ _ _))

              square9 : Square
                (cong (φ *ᶠ_) (*-comm α (ψ *ᶠ β))
                  ∙ swap φ ψ (β * α)
                  ∙ cong (ψ *ᶠ_) (shift φ β α))
                (sym
                    (cong (ψ *ᶠ_) (*-comm β (φ *ᶠ α))
                      ∙ swap ψ φ (α * β)
                      ∙ cong (φ *ᶠ_) (shift ψ α β)))
                refl
                refl
              square9 =
                ((square1 ◁ square2)
                  ∙₂ (square3 ◁v (square4 ▷ square5) ▷ refl)
                  ∙₂ (square6 ▷ square7))
                  ∙ square8
           in square9))
