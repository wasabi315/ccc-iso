module CartesianClosed.FreeCore.Normalise where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function using (_∘_)
open import Cubical.Foundations.GroupoidLaws using
  (cong-∙∙; cong-∙; rUnit; lUnit)
open import Cubical.Foundations.Isomorphism using (Iso; iso; isoToPath)

open import Cubical.Foundations.Extra using (pasteS)

import CartesianClosed.FreeCore as FC
import CartesianClosed.FreeCore.Properties as FC
import CartesianClosed.SymmetricTree as ST
import CartesianClosed.SymmetricTree.Properties as ST

private
  variable
    ℓ : Level
    A : Type ℓ

--------------------------------------------------------------------------------

module _ {A : Type ℓ} where
  open FC.Motive
  open ST.Motive

  NormaliseMotive : FC.Motive A ℓ
  NormaliseMotive .FreeCoreᴹ = ST.SForest A
  NormaliseMotive .isGroupoidFreeCoreᴹ = ST.trunc
  NormaliseMotive .ιᴹ = ST.ι
  NormaliseMotive .⊤ᴹ = ST.[]
  NormaliseMotive ._*ᴹ_ = ST._++_
  NormaliseMotive ._⇒ᴹ_ = ST._▶_
  NormaliseMotive .*-identityˡᴹ = ST.++-identityˡ
  NormaliseMotive .*-identityʳᴹ = ST.++-identityʳ
  NormaliseMotive .*-commᴹ = ST.++-comm
  NormaliseMotive .*-assocᴹ = ST.++-assoc
  NormaliseMotive .⇒-identityˡᴹ = ST.▶-identityˡ
  NormaliseMotive .⇒-curryᴹ = ST.▶-curry
  NormaliseMotive .⇒-annihilʳᴹ = ST.▶-annihilʳ
  NormaliseMotive .⇒-distribˡᴹ = ST.▶-distribˡ
  NormaliseMotive .*-bigonᴹ = ST.++-bigon
  NormaliseMotive .*-triangleᴹ = ST.++-triangle
  NormaliseMotive .*-pentagonᴹ = ST.++-pentagon
  NormaliseMotive .*-hexagonᴹ = ST.++-hexagon

  normalise : FC.FreeCore A → ST.SForest A
  normalise = FC.rec NormaliseMotive

  QuoteMotive : ST.Motive A ℓ ℓ
  QuoteMotive .STreeᴹ = FC.FreeCore A
  QuoteMotive .SForestᴹ = FC.FreeCore A
  QuoteMotive .isGroupoidSForestᴹ = FC.trunc
  QuoteMotive ._▸ᴹ_ t x = t FC.⇒ FC.ι x
  QuoteMotive .[]ᴹ = FC.⊤
  QuoteMotive ._∷ᴹ_ = FC._*_
  QuoteMotive .swapᴹ = FC.*-swap
  QuoteMotive .involᴹ = {!   !}
  QuoteMotive .ybeᴹ = {!   !}

  open ST.Rec QuoteMotive public renaming
    (recTree to quoteTree; recForest to quoteForest)


module _ {A : Type ℓ} where
  open FC.MotiveDepSet
  open ST.MotiveDepSet

  SectionMotive : ST.MotiveDepSet A ℓ ℓ
  SectionMotive .STreeᴹ t = normalise (quoteTree t) ≡ ST.[ t ]
  SectionMotive .SForestᴹ ts = normalise (quoteForest ts) ≡ ts
  SectionMotive .isSetSForestᴹ _ = ST.trunc _ _
  SectionMotive ._▸ᴹ_ ih x = cong (ST.[_] ∘ (ST._▸ x)) (ST.++-identityʳ _ ∙ ih)
  SectionMotive .[]ᴹ = refl
  SectionMotive ._∷ᴹ_ ih1 ih2 = cong₂ ST._++_ ih1 ih2
  SectionMotive .swapᴹ {t} {u} {ts} ih1 ih2 ih3 = goal
    where
      nqTree : ST.STree A → ST.SForest A
      nqTree = normalise ∘ quoteTree

      nqForest : ST.SForest A → ST.SForest A
      nqForest = normalise ∘ quoteForest

      filler : Square
        (cong₃ (λ us vs ws → us ST.++ vs ST.++ ws) ih1 ih2 ih3)
        (cong₃ (λ us vs ws → us ST.++ vs ST.++ ws) ih2 ih1 ih3)
        (sym (ST.++-assoc (nqTree t) (nqTree u) (nqForest ts))
          ∙∙ cong (ST._++ nqForest ts) (ST.++-comm (nqTree t) (nqTree u))
          ∙∙ ST.++-assoc (nqTree u) (nqTree t) (nqForest ts))
        (cong (ST._++ ts) (refl ∙ ST.swap t u ST.[] ∙ refl) ∙ refl)
      filler j i = ST.++-swap (ih1 i) (ih2 i) (ih3 i) j

      goal : Square
        (cong₃ (λ us vs ws → us ST.++ vs ST.++ ws) ih1 ih2 ih3)
        (cong₃ (λ us vs ws → us ST.++ vs ST.++ ws) ih2 ih1 ih3)
        (cong normalise
          (sym (FC.*-assoc (quoteTree t) (quoteTree u) (quoteForest ts))
            ∙∙ cong (FC._* quoteForest ts) (FC.*-comm (quoteTree t) (quoteTree u))
            ∙∙ FC.*-assoc (quoteTree u) (quoteTree t) (quoteForest ts)))
        (ST.swap t u ts)
      goal =
        pasteS refl refl
          (sym
            (cong-∙∙ normalise
              (sym (FC.*-assoc (quoteTree t) (quoteTree u) (quoteForest ts)))
              (cong (FC._* quoteForest ts) (FC.*-comm (quoteTree t) (quoteTree u)))
              (FC.*-assoc (quoteTree u) (quoteTree t) (quoteForest ts))))
          (sym (rUnit _)
            ∙ cong-∙ (ST._++ ts) refl (ST.swap t u ST.[] ∙ refl)
            ∙ sym (lUnit _)
            ∙ cong-∙ (ST._++ ts) (ST.swap t u ST.[]) refl
            ∙ sym (rUnit _))
          filler

  open ST.ElimSet SectionMotive public renaming
    (elimTreeSet to sectionTree; elimForestSet to sectionForest)

  RetractMotive : FC.MotiveDepSet A ℓ
  RetractMotive .FreeCoreᴹ t = quoteForest (normalise t) ≡ t
  RetractMotive .isSetFreeCoreᴹ _ = FC.trunc _ _
  RetractMotive .ιᴹ = {!   !}
  RetractMotive .⊤ᴹ = {!   !}
  RetractMotive ._*ᴹ_ = {!   !}
  RetractMotive ._⇒ᴹ_ = {!   !}
  RetractMotive .*-identityˡᴹ = {!   !}
  RetractMotive .*-identityʳᴹ = {!   !}
  RetractMotive .*-commᴹ = {!   !}
  RetractMotive .*-assocᴹ = {!   !}
  RetractMotive .⇒-identityˡᴹ = {!   !}
  RetractMotive .⇒-curryᴹ = {!   !}
  RetractMotive .⇒-annihilʳᴹ = {!   !}
  RetractMotive .⇒-distribˡᴹ = {!   !}

  retract : (t : FC.FreeCore A) → quoteForest (normalise t) ≡ t
  retract = FC.elimSet RetractMotive


FreeCoreIsoSForest : Iso (FC.FreeCore A) (ST.SForest A)
FreeCoreIsoSForest = iso normalise quoteForest sectionForest retract

FreeCore≡SForest : FC.FreeCore A ≡ ST.SForest A
FreeCore≡SForest = isoToPath FreeCoreIsoSForest
