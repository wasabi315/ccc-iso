module SymmetricMonoidal.SymmetricList.SetTruncation where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism using (Iso; iso; isoToPath)
open import Cubical.HITs.FiniteMultiset as FMSet using
  (FMSet; []; _∷_; comm; trunc)
open import Cubical.HITs.SetTruncation as ST using (∥_∥₂; ∣_∣₂; squash₂)
open import Cubical.Relation.Nullary using (Discrete)

open import Cubical.HITs.FiniteMultiset.Properties.Extra using (discreteFMSet)

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

module _ (discreteA : Discrete A) where

  discrete∥SList∥ : Discrete (∥ SList A ∥₂)
  discrete∥SList∥ =
    transport
      (λ i → Discrete (FMSet≡∥SList∥ A (~ i)))
      (discreteFMSet discreteA)
