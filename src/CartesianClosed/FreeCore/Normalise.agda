module CartesianClosed.FreeCore.Normalise where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function using (_∘_)
open import Cubical.Foundations.HLevels using (isSetΠ)
open import Cubical.Foundations.GroupoidLaws using
  (cong-∙∙; cong-∙; rUnit; lUnit)
open import Cubical.Foundations.Isomorphism using (Iso; iso; isoToPath)

open import Cubical.Foundations.Extra using (pasteS)

open import CartesianClosed.FreeCore as FC hiding (Motive; MotiveDepSet)
open import CartesianClosed.FreeCore.Properties
open import CartesianClosed.SymmetricTree as ST hiding (Motive; MotiveDepSet)
open import CartesianClosed.SymmetricTree.Properties
import SymmetricMonoidal.SymmetricList as SList

private
  variable
    ℓ : Level
    A : Type ℓ

--------------------------------------------------------------------------------

module _ {A : Type ℓ} where
  open FC.Motive

  Normalise : FC.Motive A ℓ
  Normalise .FreeCoreᴹ = SForest A
  Normalise .isGroupoidFreeCoreᴹ = trunc
  Normalise .ιᴹ = ST.ι
  Normalise .⊤ᴹ = []
  Normalise ._*ᴹ_ = _++_
  Normalise ._⇒ᴹ_ = _▶_
  Normalise .*-identityˡᴹ = ++-identityˡ
  Normalise .*-identityʳᴹ = ++-identityʳ
  Normalise .*-commᴹ = ++-comm
  Normalise .*-assocᴹ = ++-assoc
  Normalise .⇒-identityˡᴹ = ▶-identityˡ
  Normalise .⇒-curryᴹ = ▶-curry
  Normalise .⇒-annihilʳᴹ = ▶-annihilʳ
  Normalise .⇒-distribˡᴹ = ▶-distribˡ
  Normalise .*-bigonᴹ = ++-bigon
  Normalise .*-triangleᴹ = ++-triangle
  Normalise .*-pentagonᴹ = ++-pentagon
  Normalise .*-hexagonᴹ = ++-hexagon

  ↑_ : FreeCore A → SForest A
  ↑_ = FC.rec Normalise


module _ {A : Type ℓ} where
  open ST.Motive

  Readback : ST.Motive A ℓ ℓ
  Readback .STreeᴹ = FreeCore A
  Readback .SForestᴹ = FreeCore A
  Readback .isGroupoidSForestᴹ = trunc
  Readback ._▸ᴹ_ t x = t ⇒ FC.ι x
  Readback .[]ᴹ = ⊤
  Readback ._∷ᴹ_ = _*_
  Readback .swapᴹ = *-swap
  Readback .involᴹ = {!   !}
  Readback .ybeᴹ = {!   !}

  open ST.Rec Readback public renaming
    (recTree to ↓ᵗ_; recForest to ↓ᶠ_)


module _ {A : Type ℓ} where
  open ST.MotiveDepSet

  Section : ST.MotiveDepSet A ℓ ℓ
  Section .STreeᴹ t = ↑ ↓ᵗ t ≡ [ t ]
  Section .SForestᴹ ts = ↑ ↓ᶠ ts ≡ ts
  Section .isSetSForestᴹ _ = trunc _ _
  Section ._▸ᴹ_ ih x = cong ([_] ∘ (_▸ x)) (++-identityʳ _ ∙ ih)
  Section .[]ᴹ = refl
  Section ._∷ᴹ_ ih1 ih2 = cong₂ _++_ ih1 ih2
  Section .swapᴹ {t} {u} {ts} ih1 ih2 ih3 = goal
    where
      filler : Square
        (cong₃ (λ us vs ws → us ++ vs ++ ws) ih1 ih2 ih3)
        (cong₃ (λ us vs ws → us ++ vs ++ ws) ih2 ih1 ih3)
        (sym (++-assoc (↑ ↓ᵗ t) (↑ ↓ᵗ u) (↑ ↓ᶠ ts))
          ∙∙ cong (_++ ↑ ↓ᶠ ts) (++-comm (↑ ↓ᵗ t) (↑ ↓ᵗ u))
          ∙∙ ++-assoc (↑ ↓ᵗ u) (↑ ↓ᵗ t) (↑ ↓ᶠ ts))
        (cong (_++ ts) (refl ∙ swap t u [] ∙ refl) ∙ refl)
      filler j i = ++-swap (ih1 i) (ih2 i) (ih3 i) j

      goal : Square
        (cong₃ (λ us vs ws → us ++ vs ++ ws) ih1 ih2 ih3)
        (cong₃ (λ us vs ws → us ++ vs ++ ws) ih2 ih1 ih3)
        (cong ↑_
          (sym (*-assoc (↓ᵗ t) (↓ᵗ u) (↓ᶠ ts))
            ∙∙ cong (_* ↓ᶠ ts) (*-comm (↓ᵗ t) (↓ᵗ u))
            ∙∙ *-assoc (↓ᵗ u) (↓ᵗ t) (↓ᶠ ts)))
        (swap t u ts)
      goal =
        pasteS refl refl
          (sym
            (cong-∙∙ ↑_
              (sym (*-assoc (↓ᵗ t) (↓ᵗ u) (↓ᶠ ts)))
              (cong (_* ↓ᶠ ts) (*-comm (↓ᵗ t) (↓ᵗ u)))
              (*-assoc (↓ᵗ u) (↓ᵗ t) (↓ᶠ ts))))
          (sym (rUnit _)
            ∙ cong-∙ (_++ ts) refl (swap t u [] ∙ refl)
            ∙ sym (lUnit _)
            ∙ cong-∙ (_++ ts) (swap t u []) refl
            ∙ sym (rUnit _))
          filler

  open ST.ElimSet Section public renaming
    (elimTreeSet to ↑↓ᵗ; elimForestSet to ↑↓ᶠ)

↓-homo-++ : (ts us : SForest A) → ↓ᶠ ts * ↓ᶠ us ≡ ↓ᶠ (ts ++ us)
↓-homo-++ =
  SList.elimSet (λ _ → isSetΠ λ _ → trunc _ _)
    (λ _ → *-identityˡ _)
    (λ t ih us → *-assoc _ _ _ ∙ cong (↓ᵗ t *_) (ih us))
    {!   !}

↓-homo-► : (ts : SForest A) (t : STree A) → ↓ᶠ ts ⇒ ↓ᵗ t ≡ ↓ᵗ (ts ► t)
↓-homo-► ts (us ▸ x) =
  ⇒-curry _ _ _ ∙ cong (_⇒ FreeCore.ι x) (↓-homo-++ ts us)

↓-homo-▶ : (ts us : SForest A) → ↓ᶠ ts ⇒ ↓ᶠ us ≡ ↓ᶠ (ts ▶ us)
↓-homo-▶ ts =
  SList.elimSet (λ _ → trunc _ _)
    (⇒-annihilʳ _)
    (λ u ih → ⇒-distribˡ _ _ _ ∙ cong₂ _*_ (↓-homo-► ts u) ih)
    {!   !}

module _ {A : Type ℓ} where
  open FC.MotiveDepSet

  Retract : FC.MotiveDepSet A ℓ
  Retract .FreeCoreᴹ t = t ≡ ↓ᶠ ↑ t
  Retract .isSetFreeCoreᴹ _ = trunc _ _
  Retract .ιᴹ x = ⇒-identityˡ _ ∙ sym (*-identityʳ _)
  Retract .⊤ᴹ = refl
  Retract ._*ᴹ_ {t} {u} ih1 ih2 = cong₂ _*_ ih1 ih2 ∙ ↓-homo-++ (↑ t) (↑ u)
  Retract ._⇒ᴹ_ {t} {u} ih1 ih2 = cong₂ _⇒_ ih1 ih2 ∙ ↓-homo-▶ (↑ t) (↑ u)
  Retract .*-identityˡᴹ {t} ih = goal
    where
      goal : Square
        (cong (⊤ *_) ih ∙ *-identityˡ _)
        ih
        (*-identityˡ t)
        refl
      goal = {!   !}
  Retract .*-identityʳᴹ {t} ih = goal
    where
      goal : Square
          (cong (_* ⊤) ih ∙ ↓-homo-++ (↑ t) [])
          ih
          (*-identityʳ t)
          (cong ↓ᶠ_ (++-identityʳ (↑ t)))
      goal = {!   !}
  Retract .*-commᴹ ih1 ih2 = {!   !}
  Retract .*-assocᴹ ih1 ih2 ih3 = {!   !}
  Retract .⇒-identityˡᴹ ih = {!   !}
  Retract .⇒-curryᴹ ih1 ih2 ih3 = {!   !}
  Retract .⇒-annihilʳᴹ ih = {!   !}
  Retract .⇒-distribˡᴹ ih1 ih2 ih3 = {!   !}

  ↓↑ : (t : FreeCore A) → t ≡ ↓ᶠ ↑ t
  ↓↑ = FC.elimSet Retract


FreeCoreIsoSForest : Iso (FreeCore A) (SForest A)
FreeCoreIsoSForest = iso ↑_ ↓ᶠ_ ↑↓ᶠ (sym ∘ ↓↑)

FreeCore≡SForest : FreeCore A ≡ SForest A
FreeCore≡SForest = isoToPath FreeCoreIsoSForest
