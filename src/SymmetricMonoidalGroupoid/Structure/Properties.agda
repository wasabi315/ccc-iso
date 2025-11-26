open import Cubical.Foundations.Prelude
open import SymmetricMonoidalGroupoid.Structure

module SymmetricMonoidalGroupoid.Structure.Properties
  {ℓ} (G : SymmetricMonoidalGroupoid ℓ)
  where

open import Cubical.Foundations.Extra using (congSquare; _⟩∙∙⟨_⟩∙∙⟨_; symDistr∙∙)

open SymmetricMonoidalGroupoid G renaming (Carrier to A)

--------------------------------------------------------------------------------

*-swap : ∀ x y z → x * y * z ≡ y * x * z
*-swap x y z = sym (*-assoc x y z) ∙∙ cong (_* z) (*-comm x y) ∙∙ *-assoc y x z

abstract

  *-invol : ∀ x y z → *-swap x y z ≡ sym (*-swap y x z)
  *-invol x y z =
      *-swap x y z
    ≡⟨⟩
      (sym (*-assoc x y z) ∙∙ cong (_* z) (*-comm x y) ∙∙ *-assoc y x z)
    ≡⟨ refl ⟩∙∙⟨ congSquare (_* z) (*-bigon x y) ⟩∙∙⟨ refl ⟩
      (sym (*-assoc x y z) ∙∙ cong (_* z) (sym (*-comm y x)) ∙∙ *-assoc y x z)
    ≡⟨ sym (symDistr∙∙ _ _ _) ⟩
      sym (sym (*-assoc y x z) ∙∙ cong (_* z) (*-comm y x) ∙∙ *-assoc x y z)
    ≡⟨⟩
      sym (*-swap y x z)
    ∎

  -- *-ybe : ∀ x y z w →
  --   Path (x * y * z * w ≡ z * y * x * w)
  --     (*-swap x y (z * w)
  --       ∙∙ cong (y *_) (*-swap x z w)
  --       ∙∙ *-swap y z (x * w))
  --     (cong (x *_) (*-swap y z w)
  --       ∙∙ *-swap x z (y * w)
  --       ∙∙ cong (z *_) (*-swap x y w))
  -- *-ybe x y z w = {!   !}
