module SymmetricMonoidal.SymmetricList.SetTruncation where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function using (_∘_)
open import Cubical.Foundations.Isomorphism using
  (Iso; iso; isoToPath; transportIsoToPath; transportIsoToPath⁻)
open import Cubical.Data.Sigma using (∃-syntax; _×_)
open import Cubical.HITs.FiniteMultiset as FMSet using
  (FMSet; []; _∷_; comm; trunc)
open import Cubical.HITs.PropositionalTruncation as PT using (∥_∥₁; ∣_∣₁; squash₁)
import Cubical.HITs.PropositionalTruncation.Monad as PTMonad
open import Cubical.HITs.SetTruncation as ST using (∥_∥₂; ∣_∣₂; squash₂)
open import Cubical.HITs.Truncation using (∣_∣; PathIdTruncIso; propTruncTrunc1Iso; setTruncTrunc2Iso)
open import Cubical.Relation.Nullary using (¬_)

import Cubical.HITs.FiniteMultiset.Properties.Extra as FMSetExtra

open import SymmetricMonoidal.SymmetricList

open Iso

private
  variable
    ℓ : Level
    A : Type ℓ

infixr 5 _∣∷∣_

--------------------------------------------------------------------------------

pattern ∣[]∣ = ∣ [] ∣₂

_∣∷∣_ : A → ∥ SList A ∥₂ → ∥ SList A ∥₂
_∣∷∣_ x = ST.map (x ∷_)

∣swap∣ : (x y : A) (xs : ∥ SList A ∥₂) →
  x ∣∷∣ y ∣∷∣ xs ≡ y ∣∷∣ x ∣∷∣ xs
∣swap∣ x y =
  ST.elim (λ _ → isProp→isSet (squash₂ _ _)) (λ xs → cong ∣_∣₂ (swap x y xs))

--------------------------------------------------------------------------------
-- Iso ∥ SList A ∥₂ (FMSet A)

SList→FMSet : SList A → FMSet A
SList→FMSet = recSet trunc [] _∷_ comm

∥SList∥→FMSet : ∥ SList A ∥₂ → FMSet A
∥SList∥→FMSet = ST.rec trunc SList→FMSet

FMSet→∥SList∥ : FMSet A → ∥ SList A ∥₂
FMSet→∥SList∥ = FMSet.Rec.f squash₂ ∣[]∣ _∣∷∣_ ∣swap∣

∥SList∥→FMSet-cons : (x : A) (xs : ∥ SList A ∥₂) →
  ∥SList∥→FMSet (x ∣∷∣ xs) ≡ x ∷ ∥SList∥→FMSet xs
∥SList∥→FMSet-cons x =
  ST.elim (λ _ → isProp→isSet (trunc _ _)) (λ _ → refl)

section : (xs : FMSet A) → ∥SList∥→FMSet (FMSet→∥SList∥ xs) ≡ xs
section =
  FMSet.ElimProp.f
    (trunc _ _)
    refl
    (λ x {xs} ih → ∥SList∥→FMSet-cons x (FMSet→∥SList∥ xs) ∙ cong (x ∷_) ih)

retract' : (xs : SList A) → FMSet→∥SList∥ (SList→FMSet xs) ≡ ∣ xs ∣₂
retract' = elimProp (λ _ → squash₂ _ _) refl (λ x → cong (x ∣∷∣_))

retract : (xs : ∥ SList A ∥₂) → FMSet→∥SList∥ (∥SList∥→FMSet xs) ≡ xs
retract = ST.elim (λ _ → isProp→isSet (squash₂ _ _)) retract'

FMSetIso∥SList∥ : (A : Type ℓ) → Iso ∥ SList A ∥₂ (FMSet A)
FMSetIso∥SList∥ _ = iso ∥SList∥→FMSet FMSet→∥SList∥ section retract

FMSet≡∥SList∥ : (A : Type ℓ) → ∥ SList A ∥₂ ≡ FMSet A
FMSet≡∥SList∥ _ = isoToPath (FMSetIso∥SList∥ _)

--------------------------------------------------------------------------------

Path∥₂→∥Path∥₁ : {x y : A} → ∣ x ∣₂ ≡ ∣ y ∣₂ → ∥ x ≡ y ∥₁
Path∥₂→∥Path∥₁ {x = x} {y = y} =
  inv propTruncTrunc1Iso
    ∘ fun (PathIdTruncIso 1)
    ∘ cong (fun setTruncTrunc2Iso)

module _ {A : Type ℓ} where

  consPath : PathP (λ i → A → FMSet≡∥SList∥ A i → FMSet≡∥SList∥ A i) _∣∷∣_ _∷_
  consPath = funExt λ x → toPathP (funExt λ xs →
      transport (FMSet≡∥SList∥ A)
        (x ∣∷∣ transport (sym (FMSet≡∥SList∥ A)) xs)
    ≡⟨ transportIsoToPath (FMSetIso∥SList∥ A)
        (x ∣∷∣ transport (sym (FMSet≡∥SList∥ A)) xs)
    ⟩
      ∥SList∥→FMSet
        (x ∣∷∣ transport (sym (FMSet≡∥SList∥ A)) xs)
    ≡⟨ cong (∥SList∥→FMSet ∘ (x ∣∷∣_)) (transportIsoToPath⁻ (FMSetIso∥SList∥ A) xs) ⟩
      ∥SList∥→FMSet (x ∣∷∣ FMSet→∥SList∥ xs)
    ≡⟨ ∥SList∥→FMSet-cons x (FMSet→∥SList∥ xs) ⟩
      x ∷ ∥SList∥→FMSet (FMSet→∥SList∥ xs)
    ≡⟨ cong (x ∷_) (section xs) ⟩
      x ∷ xs
    ∎)

  drop-∷ : (x : A) (xs ys : ∥ SList A ∥₂) → x ∣∷∣ xs ≡ x ∣∷∣ ys → xs ≡ ys
  drop-∷ =
    transport
      (λ i →
        (x : A) (xs ys : FMSet≡∥SList∥ A (~ i)) →
        consPath (~ i) x xs ≡ consPath (~ i) x ys →
        xs ≡ ys)
      FMSetExtra.drop-∷

  drop-∷' : (x : A) (xs ys : SList A) → ∥ x ∷ xs ≡ x ∷ ys ∥₁ → ∥ xs ≡ ys ∥₁
  drop-∷' x xs ys p =
    p >>= λ p → Path∥₂→∥Path∥₁ (drop-∷ x ∣ xs ∣₂ ∣ ys ∣₂ (cong ∣_∣₂ p))
    where open PTMonad

  differentHead : (x y : A) (xs ys : ∥ SList A ∥₂) →
    ¬ x ≡ y →
    x ∣∷∣ xs ≡ y ∣∷∣ ys →
    ∃[ zs ∈ _ ] (xs ≡ y ∣∷∣ zs) × (x ∣∷∣ zs ≡ ys)
  differentHead =
    transport
      (λ i →
        (x y : A) (xs ys : FMSet≡∥SList∥ A (~ i)) →
        ¬ x ≡ y →
        consPath (~ i) x xs ≡ consPath (~ i) y ys →
        ∃[ zs ∈ _ ] (xs ≡ consPath (~ i) y zs) × (consPath (~ i) x zs ≡ ys))
      FMSetExtra.differentHead

  differentHead' : (x y : A) (xs ys : SList A) →
    ¬ x ≡ y →
    ∥ x ∷ xs ≡ y ∷ ys ∥₁ →
    ∃[ zs ∈ _ ] (xs ≡ y ∷ zs) × (x ∷ zs ≡ ys)
  differentHead' x y xs ys neq p =
    p >>= λ p →
    differentHead x y ∣ xs ∣₂ ∣ ys ∣₂ neq (cong ∣_∣₂ p) >>=
    ST.sigmaElim (λ _ → isProp→isSet squash₁) λ zs (p , q) →
      Path∥₂→∥Path∥₁ p >>= λ p →
      Path∥₂→∥Path∥₁ q >>= λ q →
      return (zs , p , q)
    where open PTMonad
