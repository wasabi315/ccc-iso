module CartesianClosedCore.Free.Properties where

open import Cubical.Foundations.Prelude

open import CartesianClosedCore.Free

private
  variable
    ℓ : Level
    A : Type ℓ

--------------------------------------------------------------------------------
-- Basic properties

module _ {A : Type ℓ} where
  open import SymmetricMonoidalGroupoid.Structure.Properties (symmetricMonoidalGroupoid A) public
