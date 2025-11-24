module CartesianClosed.SymmetricTree.SetInterpretation where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels using (hSet; isGroupoidHSet; isSet→)

open import CartesianClosed.SymmetricTree
open import SymmetricMonoidal.SymmetricList.SetInterpretation using
  (Unitˢ; _×ˢ_; ×ˢ-swap; ×ˢ-invol; ×ˢ-ybe)

private
  variable
    ℓ ℓ′ : Level

infixr 0 _→ˢ_

--------------------------------------------------------------------------------

_→ˢ_ : (A : hSet ℓ) (B : hSet ℓ′) → hSet (ℓ-max ℓ ℓ′)
(A , ASet) →ˢ (B , BSet) = (A → B) , isSet→ BSet

--------------------------------------------------------------------------------

module _ {ℓ} where
  open Motive

  SetModel : Motive (hSet ℓ) (ℓ-suc ℓ) (ℓ-suc ℓ)
  SetModel .STreeᴹ = hSet ℓ
  SetModel .SForestᴹ = hSet ℓ
  SetModel .isGroupoidSForestᴹ = isGroupoidHSet
  SetModel ._▸ᴹ_ = _→ˢ_
  SetModel .[]ᴹ = Unitˢ
  SetModel ._∷ᴹ_ = _×ˢ_
  SetModel .swapᴹ = ×ˢ-swap
  SetModel .involᴹ = ×ˢ-invol
  SetModel .ybeᴹ = ×ˢ-ybe

  open Rec SetModel renaming (recTree to ⟦_⟧ᵗ; recForest to ⟦_⟧ᶠ) public
