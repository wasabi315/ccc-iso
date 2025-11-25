module SymmetricMonoidal.FreeGroupoid.Properties where

open import Cubical.Foundations.Prelude

open import SymmetricMonoidal.FreeGroupoid

private
  variable
    ℓ : Level
    A : Type ℓ

--------------------------------------------------------------------------------
-- Basic properties

module _ {A : Type ℓ} where
  open import SymmetricMonoidal.GroupoidStructure.Properties (symmetricMonoidalGroupoid A) public
