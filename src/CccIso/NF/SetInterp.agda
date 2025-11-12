module CccIso.NF.SetInterp where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv using
  (_≃_; idEquiv; _∙ₑ_; equivEq; compEquivIdEquiv)
open import Cubical.Foundations.HLevels using
  (HLevel; TypeOfHLevel; hSet; isPropIsOfHLevel; TypeOfHLevel≡;
    isSet→SquareP; isSet×; isSet→; isGroupoidHSet)
open import Cubical.Foundations.Isomorphism using (Iso; iso)
open import Cubical.Foundations.GroupoidLaws using (lUnit)
open import Cubical.Foundations.GroupoidLaws using (cong-∙∙)
open import Cubical.Foundations.Univalence using
  (ua; uaIdEquiv; uaInvEquiv; EquivJ)
open import Cubical.Data.Fin.Recursive.Base using (Fin)
open import Cubical.Data.Nat.Base using (ℕ)
open import Cubical.Data.Unit using (Unit; isSetUnit)
open import Cubical.Data.Sigma using (_×_; _,_; Σ-cong-equiv-snd)
open import Cubical.Reflection.StrictEquiv

open import CccIso.NF

private
  variable
    n : ℕ
    ℓ a b c d : Level
    A B C D : Type ℓ

infixr 5 _→ˢ_
infixr 6 _×ˢ_

--------------------------------------------------------------------------------
-- Utilities

TypeOfHLevel≡≡ : (n : HLevel) {A B : TypeOfHLevel a n} {p q : A ≡ B} →
  cong fst p ≡ cong fst q → p ≡ q
TypeOfHLevel≡≡ n {p = p} {q = q} P j i =
  P j i ,
  isSet→SquareP
    (λ k l → isProp→isSet (isPropIsOfHLevel {A = P k l} n))
    (cong snd p) (cong snd q)
    refl refl
    j i

uaDoubleCompEquiv : (e : A ≃ B) (f : B ≃ C) (g : C ≃ D) →
  ua (e ∙ₑ f ∙ₑ g) ≡ ua e ∙∙ ua f ∙∙ ua g
uaDoubleCompEquiv =
  EquivJ
    (λ _ e → ∀ f g → ua (e ∙ₑ f ∙ₑ g) ≡ ua e ∙∙ ua f ∙∙ ua g)
    (EquivJ
      (λ _ f → ∀ g →
        ua (idEquiv _ ∙ₑ f ∙ₑ g) ≡ ua (idEquiv _) ∙∙ ua f ∙∙ ua g)
      (λ g →
        cong ua (compEquivIdEquiv _ ∙ compEquivIdEquiv _)
          ∙∙ lUnit (ua g)
          ∙∙ sym (cong₂ (_∙∙_∙∙ ua g) uaIdEquiv uaIdEquiv)))

×-cong-equiv-snd : A ≃ B → C × A ≃ C × B
×-cong-equiv-snd e = Σ-cong-equiv-snd λ _ → e

ua×-cong-equiv-snd : (e : A ≃ B) → ua (×-cong-equiv-snd e) ≡ cong (C ×_) (ua e)
ua×-cong-equiv-snd =
  EquivJ
    (λ _ e → ua (×-cong-equiv-snd e) ≡ cong (_ ×_) (ua e))
    (cong ua (equivEq refl) ∙∙ uaIdEquiv ∙∙ cong (cong (_ ×_)) (sym uaIdEquiv))

--------------------------------------------------------------------------------

module _ (A : Type a) (B : Type b) (C : Type c) where

  ×-swap-Iso : Iso (A × B × C) (B × A × C)
  ×-swap-Iso = iso
    (λ (x , y , z) → y , x , z)
    (λ (y , x , z) → x , y , z)
    (λ _ → refl)
    (λ _ → refl)

  unquoteDecl ×-swap-≃ = declStrictIsoToEquiv ×-swap-≃ ×-swap-Iso


×-swap : (A : Type a) (B : Type b) (C : Type c) → A × B × C ≡ B × A × C
×-swap A B C = ua (×-swap-≃ A B C)

×-invol : (A : Type a) (B : Type b) (C : Type c) →
  ×-swap A B C ≡ sym (×-swap B A C)
×-invol A B C = cong ua (equivEq refl) ∙ uaInvEquiv (×-swap-≃ B A C)

×-hexagon : (A : Type a) (B : Type b) (C : Type c) (D : Type d) →
  Path (A × B × C × D ≡ C × B × A × D)
    (×-swap A B (C × D)
      ∙∙ cong (B ×_) (×-swap A C D)
      ∙∙ ×-swap B C (A × D))
    (cong (A ×_) (×-swap B C D)
      ∙∙ ×-swap A C (B × D)
      ∙∙ cong (C ×_) (×-swap A B D))
×-hexagon A B C D =
    (ua (×-swap-≃ A B (C × D))
        ∙∙ cong (B ×_) (ua (×-swap-≃ A C D))
        ∙∙ ua (×-swap-≃ B C (A × D)))
  ≡⟨ cong
      (ua (×-swap-≃ A B (C × D)) ∙∙_∙∙ ua (×-swap-≃ B C (A × D)))
      (sym (ua×-cong-equiv-snd (×-swap-≃ A C D)))
  ⟩
    (ua (×-swap-≃ A B (C × D))
        ∙∙ ua (×-cong-equiv-snd (×-swap-≃ A C D))
        ∙∙ ua (×-swap-≃ B C (A × D)))
  ≡⟨ sym (uaDoubleCompEquiv _ _ _) ⟩
    (ua
      (×-swap-≃ A B (C × D)
        ∙ₑ ×-cong-equiv-snd (×-swap-≃ A C D)
        ∙ₑ ×-swap-≃ B C (A × D)))
  ≡⟨ cong ua (equivEq refl) ⟩
    (ua
      (×-cong-equiv-snd (×-swap-≃ B C D)
        ∙ₑ ×-swap-≃ A C (B × D)
        ∙ₑ ×-cong-equiv-snd (×-swap-≃ A B D)))
  ≡⟨ uaDoubleCompEquiv _ _ _ ⟩
    (ua (×-cong-equiv-snd (×-swap-≃ B C D))
      ∙∙ ua (×-swap-≃ A C (B × D))
      ∙∙ ua (×-cong-equiv-snd (×-swap-≃ A B D)))
  ≡⟨ cong₂
      (λ p (q : C × A × B × D ≡ C × B × A × D) →
        p ∙∙ ua (×-swap-≃ A C (B × D)) ∙∙ q)
      (ua×-cong-equiv-snd (×-swap-≃ B C D))
      (ua×-cong-equiv-snd (×-swap-≃ A B D))
  ⟩
    (cong (A ×_) (ua (×-swap-≃ B C D))
      ∙∙ ua (×-swap-≃ A C (B × D))
      ∙∙ cong (C ×_) (ua (×-swap-≃ A B D)))
  ∎

--------------------------------------------------------------------------------
-- Interpretation into hSet

Unitˢ : hSet ℓ-zero
Unitˢ = Unit , isSetUnit

_×ˢ_ : (A : hSet a) (B : hSet b) → hSet (ℓ-max a b)
(A , ASet) ×ˢ (B , BSet) = (A × B) , isSet× ASet BSet

_→ˢ_ : (A : hSet a) (B : hSet b) → hSet (ℓ-max a b)
(A , ASet) →ˢ (B , BSet) = (A → B) , isSet→ BSet

-- This opaque is essential for performance
-- With opaque it takes only 20ms to check ⟦_⟧ⁿ, while it takes
-- indefinitely and eats up CPU/RAM like crazy without opaque!!
opaque

  ×ˢ-swap : (A : hSet a) (B : hSet b) (C : hSet c) →
    A ×ˢ B ×ˢ C ≡ B ×ˢ A ×ˢ C
  ×ˢ-swap A B C = TypeOfHLevel≡ 2 (×-swap _ _ _)

  ×ˢ-invol : (A : hSet a) (B : hSet b) (C : hSet c) →
    ×ˢ-swap A B C ≡ sym (×ˢ-swap B A C)
  ×ˢ-invol A B C =
    TypeOfHLevel≡≡ 2 (×-invol (A .fst) (B .fst) (C .fst))

  ×ˢ-hexagon : (A : hSet a) (B : hSet b) (C : hSet c) (D : hSet d) →
    Path (A ×ˢ B ×ˢ C ×ˢ D ≡ C ×ˢ B ×ˢ A ×ˢ D)
      (×ˢ-swap A B (C ×ˢ D)
        ∙∙ cong (B ×ˢ_) (×ˢ-swap A C D)
        ∙∙ ×ˢ-swap B C (A ×ˢ D))
      (cong (A ×ˢ_) (×ˢ-swap B C D)
        ∙∙ ×ˢ-swap A C (B ×ˢ D)
        ∙∙ cong (C ×ˢ_) (×ˢ-swap A B D))
  ×ˢ-hexagon A B C D =
    TypeOfHLevel≡≡ 2 (×-hexagon (A .fst) (B .fst) (C .fst) (D .fst))


{-# TERMINATING #-}
⟦_⟧ᶠ : (φ : Factor n) (ρ : Fin n → hSet ℓ-zero) → hSet ℓ-zero
⟦_⟧ⁿ : (α : NF n) (ρ : Fin n → hSet ℓ-zero) → hSet ℓ-zero

⟦ α ⇒ι x ⟧ᶠ ρ = ⟦ α ⟧ⁿ ρ →ˢ ρ x

⟦ ⊤ ⟧ⁿ ρ = Unitˢ
⟦ φ *ᶠ α ⟧ⁿ ρ = ⟦ φ ⟧ᶠ ρ ×ˢ ⟦ α ⟧ⁿ ρ
⟦ swap φ ψ α i ⟧ⁿ ρ = ×ˢ-swap (⟦ φ ⟧ᶠ ρ) (⟦ ψ ⟧ᶠ ρ) (⟦ α ⟧ⁿ ρ) i
⟦ invol φ ψ α i j ⟧ⁿ ρ = ×ˢ-invol (⟦ φ ⟧ᶠ ρ) (⟦ ψ ⟧ᶠ ρ) (⟦ α ⟧ⁿ ρ) i j
⟦ hexagon ε φ ψ α i j ⟧ⁿ ρ = path i j
  where
    path :
        cong (λ β → ⟦ β ⟧ⁿ ρ)
          (swap ε φ (ψ *ᶠ α)
            ∙∙ cong (φ *ᶠ_) (swap ε ψ α)
            ∙∙ swap φ ψ (ε *ᶠ α))
      ≡
        cong (λ β → ⟦ β ⟧ⁿ ρ)
          (cong (ε *ᶠ_) (swap φ ψ α)
            ∙∙ swap ε ψ (φ *ᶠ α)
            ∙∙ cong (ψ *ᶠ_) (swap ε φ α))
    path =
      cong-∙∙ (λ β → ⟦ β ⟧ⁿ ρ) _ _ _
        ∙∙ ×ˢ-hexagon (⟦ ε ⟧ᶠ ρ) (⟦ φ ⟧ᶠ ρ) (⟦ ψ ⟧ᶠ ρ) (⟦ α ⟧ⁿ ρ)
        ∙∙ sym (cong-∙∙ (λ β → ⟦ β ⟧ⁿ ρ) _ _ _)
⟦ trunc α β p q P Q i j k ⟧ⁿ ρ =
  isGroupoidHSet
    (⟦ α ⟧ⁿ ρ) (⟦ β ⟧ⁿ ρ)
    (λ i → ⟦ p i ⟧ⁿ ρ) (λ i → ⟦ q i ⟧ⁿ ρ)
    (λ i j → ⟦ P i j ⟧ⁿ ρ) (λ i j → ⟦ Q i j ⟧ⁿ ρ)
    i j k
