module SymmetricMonoidal.SymmetricList.SetInterpretation where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels using
  (hSet; isSet×; TypeOfHLevel≡; isGroupoidHSet)
open import Cubical.Foundations.Equiv using (equivEq; _∙ₑ_)
open import Cubical.Foundations.Isomorphism using (Iso; iso)
open import Cubical.Foundations.Univalence using (ua; uaInvEquiv)
open import Cubical.Data.Sigma using (_×_; _,_)
open import Cubical.Data.Unit using (Unit*; isSetUnit*)
open import Cubical.Reflection.StrictEquiv

open import Cubical.Foundations.Extra using
  (×-cong-equiv-snd; ua×-cong-equiv-snd; uaDoubleCompEquiv; TypeOfHLevel≡≡)
open import SymmetricMonoidal.SymmetricList

private
  variable
    ℓ a b c d : Level

infixr 4 _×ˢ_

--------------------------------------------------------------------------------

module _ (A : Type a) (B : Type b) (C : Type c) where

  ×-swap-Iso : Iso (A × B × C) (B × A × C)
  ×-swap-Iso = iso
    (λ (x , y , z) → y , x , z)
    (λ (y , x , z) → x , y , z)
    (λ _ → refl)
    (λ _ → refl)

  unquoteDecl ×-swap-≃ = declStrictIsoToEquiv ×-swap-≃ ×-swap-Iso

  ×-swap : A × B × C ≡ B × A × C
  ×-swap = ua ×-swap-≃


×-invol : (A : Type a) (B : Type b) (C : Type c) →
  ×-swap A B C ≡ sym (×-swap B A C)
×-invol A B C = cong ua (equivEq refl) ∙ uaInvEquiv (×-swap-≃ B A C)

×-ybe : (A : Type a) (B : Type b) (C : Type c) (D : Type d) →
  Path (A × B × C × D ≡ C × B × A × D)
    (×-swap A B (C × D)
      ∙∙ cong (B ×_) (×-swap A C D)
      ∙∙ ×-swap B C (A × D))
    (cong (A ×_) (×-swap B C D)
      ∙∙ ×-swap A C (B × D)
      ∙∙ cong (C ×_) (×-swap A B D))
×-ybe A B C D =
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

Unitˢ : hSet ℓ
Unitˢ = Unit* , isSetUnit*

_×ˢ_ : (A : hSet a) (B : hSet b) → hSet (ℓ-max a b)
(A , ASet) ×ˢ (B , BSet) = (A × B) , isSet× ASet BSet

×ˢ-swap : (A : hSet a) (B : hSet b) (C : hSet c) →
  (A ×ˢ B ×ˢ C) ≡ (B ×ˢ A ×ˢ C)
×ˢ-swap A B C = TypeOfHLevel≡ 2 (×-swap _ _ _)

×ˢ-invol : (A : hSet a) (B : hSet b) (C : hSet c) →
  ×ˢ-swap A B C ≡ sym (×ˢ-swap B A C)
×ˢ-invol A B C =
  TypeOfHLevel≡≡ 2 (×-invol (A .fst) (B .fst) (C .fst))

×ˢ-ybe : (A : hSet a) (B : hSet b) (C : hSet c) (D : hSet d) →
  Path ((A ×ˢ B ×ˢ C ×ˢ D) ≡ (C ×ˢ B ×ˢ A ×ˢ D))
    (×ˢ-swap A B (C ×ˢ D)
      ∙∙ cong (B ×ˢ_) (×ˢ-swap A C D)
      ∙∙ ×ˢ-swap B C (A ×ˢ D))
    (cong (A ×ˢ_) (×ˢ-swap B C D)
      ∙∙ ×ˢ-swap A C (B ×ˢ D)
      ∙∙ cong (C ×ˢ_) (×ˢ-swap A B D))
×ˢ-ybe A B C D =
  TypeOfHLevel≡≡ 2 (×-ybe (A .fst) (B .fst) (C .fst) (D .fst))

⟦_⟧ : SList (hSet ℓ) → hSet ℓ
⟦_⟧ = rec isGroupoidHSet Unitˢ _×ˢ_ ×ˢ-swap ×ˢ-invol ×ˢ-ybe
