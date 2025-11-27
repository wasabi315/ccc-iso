module SymmetricMonoidalGroupoid.Free.Normalise where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function using (_∘_)
open import Cubical.Foundations.HLevels using (isSetΠ)
open import Cubical.Foundations.GroupoidLaws using
  (cong-∙∙; cong-∙; rUnit; lUnit)
open import Cubical.Foundations.Isomorphism using (Iso; iso; isoToPath)

open import Cubical.Foundations.Extra using (pasteS; _∙h_)

open import SymmetricMonoidalGroupoid.SymmetricList as SL
open import SymmetricMonoidalGroupoid.SymmetricList.Properties
open import SymmetricMonoidalGroupoid.Free as FG
open import SymmetricMonoidalGroupoid.Free.Properties

private
  variable
    ℓ : Level
    A : Type ℓ

--------------------------------------------------------------------------------

module _ {A : Type ℓ} where
  open FG.Motive

  Normalise : FG.Motive A ℓ
  Normalise .Freeᴹ = SList A
  Normalise .isGroupoidFreeᴹ = trunc
  Normalise .ιᴹ = [_]
  Normalise .⊤ᴹ = []
  Normalise ._*ᴹ_ = _++_
  Normalise .*-identityˡᴹ = ++-identityˡ
  Normalise .*-identityʳᴹ = ++-identityʳ
  Normalise .*-commᴹ = ++-comm
  Normalise .*-assocᴹ = ++-assoc
  Normalise .*-bigonᴹ = ++-bigon
  Normalise .*-triangleᴹ = ++-triangle
  Normalise .*-pentagonᴹ = ++-pentagon
  Normalise .*-hexagonᴹ = ++-hexagon

  ↑_ : Free A → SList A
  ↑_ = FG.rec Normalise


↓_ : SList A → Free A
↓_ = SL.rec trunc
  ⊤
  (λ x → ι x *_)
  (λ x y → *-swap (ι x) (ι y))
  (λ x y → *-invol (ι x) (ι y))
  (λ x y z → {!   !})

↑↓ : (xs : SList A) → ↑ ↓ xs ≡ xs
↑↓ = SL.elimSet (λ _ → trunc _ _)
  refl
  (λ x → cong (x ∷_))
  (λ x y {t} ih →
    let filler : Square
          (cong (λ u → x ∷ y ∷ u) ih)
          (cong (λ u → y ∷ x ∷ u) ih)
          (cong (_++ ↑ ↓ t) (refl ∙ swap x y [] ∙ refl) ∙ refl)
          (cong (_++ t) (refl ∙ swap x y [] ∙ refl) ∙ refl)
        filler j i = ++-swap [ x ] [ y ] (ih i) j

        goal : Square
          (cong (λ u → x ∷ y ∷ u) ih)
          (cong (λ u → y ∷ x ∷ u) ih)
          (cong ↑_
            (sym (*-assoc (ι x) (ι y) (↓ t))
              ∙∙ cong (_* ↓ t) (*-comm (ι x) (ι y))
              ∙∙ *-assoc (ι y) (ι x) (↓ t)))
          (swap x y t)
        goal = pasteS refl refl
          (sym
            (cong-∙∙ ↑_
                (sym (*-assoc (ι x) (ι y) (↓ t)))
                (cong (_* ↓ t) (*-comm (ι x) (ι y)))
                (*-assoc (ι y) (ι x) (↓ t))))
          (sym
            (cong {y = refl ∙ swap x y [] ∙ refl} (cong (_++ t))
                (rUnit _ ∙ lUnit _)
              ∙ rUnit _))
          filler
     in goal)

↓-homo-++ : (xs ys : SList A) → ↓ xs * ↓ ys ≡ ↓ (xs ++ ys)
↓-homo-++ = SL.elimSet (λ _ → isSetΠ λ _ → trunc _ _)
  (λ _ → *-identityˡ _)
  (λ x ih us → *-assoc _ _ _ ∙ cong (ι x *_) (ih us))
  (λ x y {xs} ih → funExt λ ys → {!   !})

module _ {A : Type ℓ} where
  open FG.MotiveDepSet

  Retract : FG.MotiveDepSet A ℓ
  Retract .Freeᴹ t = t ≡ ↓ ↑ t
  Retract .isSetFreeᴹ _ = trunc _ _
  Retract .ιᴹ x = sym (*-identityʳ _)
  Retract .⊤ᴹ = refl
  Retract ._*ᴹ_ {t} {u} ih1 ih2 = cong₂ _*_ ih1 ih2 ∙ ↓-homo-++ (↑ t) (↑ u)
  Retract .*-identityˡᴹ = {!   !}
  Retract .*-identityʳᴹ = {!   !}
  Retract .*-commᴹ = {!   !}
  Retract .*-assocᴹ = {!   !}

  ↓↑ : (t : Free A) → t ≡ ↓ ↑ t
  ↓↑ = FG.elimSet Retract


FreeIsoSList : Iso (Free A) (SList A)
FreeIsoSList = iso ↑_ ↓_ ↑↓ (sym ∘ ↓↑)

Free≡SList : Free A ≡ SList A
Free≡SList = isoToPath FreeIsoSList
