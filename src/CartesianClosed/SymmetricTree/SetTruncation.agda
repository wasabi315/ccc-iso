module CartesianClosed.SymmetricTree.SetTruncation where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function using (_∘_)
open import Cubical.Foundations.Isomorphism using (Iso; iso; isoToPath)
open import Cubical.Foundations.HLevels using
  (isSet→SquareP; isPropΠ; isSet→; isSet×; isOfHLevelRetract)
open import Cubical.HITs.FiniteMultiset as FMSet using
  (FMSet; []; _∷_; comm; trunc)
open import Cubical.HITs.SetTruncation as ST using (∥_∥₂; ∣_∣₂; squash₂)
open import Cubical.Relation.Nullary using
  (¬_; Discrete; Dec; yes; no; isPropDec; Discrete→isSet)

open import Cubical.HITs.FiniteMultiset.Properties.Extra using
  (module DiscreteFMSet)

open import CartesianClosed.SymmetricTree

private
  variable
    ℓ ℓ′ ℓ″ : Level
    A : Type ℓ

infixr 4 _▸_ _∣▸∣_
infixr 5 _∣∷∣_

--------------------------------------------------------------------------------

record STree' (A : Type ℓ) : Type ℓ
SForest' : Type ℓ → Type ℓ

record STree' A where
  inductive
  constructor _▸_
  field
    domain : SForest' A
    codomain : A

open STree'

SForest' A = FMSet (STree' A)

isSetSTree' : isSet A → isSet (STree' A)
isSetSTree' ASet =
  isOfHLevelRetract 2
    (λ t → domain t , codomain t)
    (λ (dom , cod) → dom ▸ cod)
    (λ _ → refl)
    (isSet× trunc ASet)

record MotiveDep' (A : Type ℓ) ℓ′ ℓ″ : Type (ℓ-suc (ℓ-max ℓ (ℓ-max ℓ′ ℓ″))) where
  no-eta-equality
  infixr 4 _▸ᴹ_
  infixr 5 _∷ᴹ_
  field
    STreeᴹ : STree' A → Type ℓ′
    SForestᴹ : SForest' A → Type ℓ″
    isSetSForestᴹ : ∀ ts → isSet (SForestᴹ ts)
    _▸ᴹ_ : ∀ {ts} (tsᴹ : SForestᴹ ts) x → STreeᴹ (ts ▸ x)
    []ᴹ : SForestᴹ []
    _∷ᴹ_ : ∀ {t ts} (tᴹ : STreeᴹ t) (tsᴹ : SForestᴹ ts) → SForestᴹ (t ∷ ts)
    swapᴹ : ∀ {t u ts} tᴹ uᴹ tsᴹ →
      PathP (λ i → SForestᴹ (comm t u ts i))
        (tᴹ ∷ᴹ (uᴹ ∷ᴹ tsᴹ))
        (uᴹ ∷ᴹ (tᴹ ∷ᴹ tsᴹ))


module ElimSet' (M : MotiveDep' A ℓ′ ℓ″) where
  open MotiveDep' M

  elimTree' : ∀ t → STreeᴹ t
  elimForest' : ∀ ts → SForestᴹ ts

  elimTree' (ts ▸ x) = elimForest' ts ▸ᴹ x

  elimForest' [] = []ᴹ
  elimForest' (t ∷ ts) = elimTree' t ∷ᴹ elimForest' ts
  elimForest' (comm t u ts i) =
    swapᴹ (elimTree' t) (elimTree' u) (elimForest' ts) i
  elimForest' (trunc ts us p q i j) =
    isSet→SquareP (λ i j → isSetSForestᴹ (trunc ts us p q i j))
      (cong elimForest' p) (cong elimForest' q)
      refl refl
      i j


record MotiveDepProp' (A : Type ℓ) ℓ′ ℓ″ : Type (ℓ-suc (ℓ-max ℓ (ℓ-max ℓ′ ℓ″))) where
  no-eta-equality
  infixr 4 _▸ᴹ_
  infixr 5 _∷ᴹ_
  field
    STreeᴹ : STree' A → Type ℓ′
    SForestᴹ : SForest' A → Type ℓ″
    isPropSForestᴹ : ∀ ts → isProp (SForestᴹ ts)
    _▸ᴹ_ : ∀ {ts} (tsᴹ : SForestᴹ ts) x → STreeᴹ (ts ▸ x)
    []ᴹ : SForestᴹ []
    _∷ᴹ_ : ∀ {t ts} (tᴹ : STreeᴹ t) (tsᴹ : SForestᴹ ts) → SForestᴹ (t ∷ ts)

  swapᴹ : ∀ {t u ts} tᴹ uᴹ tsᴹ →
    PathP (λ i → SForestᴹ (comm t u ts i))
      (tᴹ ∷ᴹ (uᴹ ∷ᴹ tsᴹ))
      (uᴹ ∷ᴹ (tᴹ ∷ᴹ tsᴹ))
  swapᴹ {t} {u} {ts} _ _ _ =
    isProp→PathP (λ i → isPropSForestᴹ (comm t u ts i)) _ _

  motiveDep : MotiveDep' A ℓ′ ℓ″
  motiveDep = record
    { STreeᴹ = STreeᴹ
    ; SForestᴹ = SForestᴹ
    ; isSetSForestᴹ = λ ts → isProp→isSet (isPropSForestᴹ ts)
    ; _▸ᴹ_ = _▸ᴹ_
    ; []ᴹ = []ᴹ
    ; _∷ᴹ_ = _∷ᴹ_
    ; swapᴹ = swapᴹ
    }


module ElimProp' (M : MotiveDepProp' A ℓ′ ℓ″) where
  open ElimSet' (MotiveDepProp'.motiveDep M) public renaming
    (elimTree' to elimTreeProp'; elimForest' to elimForestProp')


module Rec' (M : MotiveSet A ℓ′ ℓ″) where
  open MotiveSet M

  recTree' : STree' A → STreeᴹ
  recForest' : SForest' A → SForestᴹ

  recTree' (ts ▸ x) = recForest' ts ▸ᴹ x

  recForest' [] = []ᴹ
  recForest' (x ∷ ts) = recTree' x ∷ᴹ recForest' ts
  recForest' (comm x y ts i) = swapᴹ (recTree' x) (recTree' y) (recForest' ts) i
  recForest' (trunc ts us p q i j) =
    isSetSForestᴹ
      (recForest' ts) (recForest' us)
      (λ i → recForest' (p i)) (λ i → recForest' (q i))
      i j

--------------------------------------------------------------------------------

module _ {A : Type ℓ} (discreteA : Discrete A) where
  open MotiveDepProp'

  DiscreteSTree' : MotiveDepProp' A _ _
  DiscreteSTree' .STreeᴹ t = ∀ u → Dec (t ≡ u)
  DiscreteSTree' .SForestᴹ ts = ∀ us → Dec (ts ≡ us)
  DiscreteSTree' .isPropSForestᴹ = λ _ → isPropΠ λ _ → isPropDec (trunc _ _)
  DiscreteSTree' .[]ᴹ = DiscreteFMSet.nilCase
  DiscreteSTree' ._∷ᴹ_ = DiscreteFMSet.consCase _ _
  DiscreteSTree' ._▸ᴹ_ ts≟ x (us ▸ y) with discreteA x y | ts≟ us
  ... | no x≢y  | _         = no (x≢y ∘ cong codomain)
  ... | yes x≡y | no ts≢us  = no (ts≢us ∘ cong domain)
  ... | yes x≡y | yes ts≡us = yes (cong₂ _▸_ ts≡us x≡y)

  open ElimProp' DiscreteSTree' public renaming
    (elimTreeProp' to discreteSTree'; elimForestProp' to discreteSForest')

--------------------------------------------------------------------------------

_∣▸∣_ : ∥ SForest A ∥₂ → A → ∥ STree A ∥₂
_∣▸∣_ = ST.rec (isSet→ squash₂) (λ ts x → ∣ ts ▸ x ∣₂)

pattern ∣[]∣ = ∣ [] ∣₂

_∣∷∣_ : ∥ STree A ∥₂ → ∥ SForest A ∥₂ → ∥ SForest A ∥₂
_∣∷∣_ = ST.rec2 squash₂ λ t ts → ∣ t ∷ ts ∣₂

∣swap∣ : (t u : ∥ STree A ∥₂) (ts : ∥ SForest A ∥₂) →
  t ∣∷∣ u ∣∷∣ ts ≡ u ∣∷∣ t ∣∷∣ ts
∣swap∣ = ST.elim3 (λ _ _ _ → isProp→isSet (squash₂ _ _)) λ t u ts →
  cong ∣_∣₂ (swap t u ts)

module _ {A : Type ℓ} where
  open MotiveSet

  Forward : MotiveSet A _ _
  Forward .STreeᴹ = STree' A
  Forward .SForestᴹ = SForest' A
  Forward .isSetSForestᴹ = trunc
  Forward ._▸ᴹ_ = _▸_
  Forward .[]ᴹ = []
  Forward ._∷ᴹ_ = _∷_
  Forward .swapᴹ = comm

  open RecSet Forward public renaming
    (recTreeSet to STree→STree'; recForestSet to SForest→SForest')


∥STree∥→STree' : isSet A → ∥ STree A ∥₂ → STree' A
∥STree∥→STree' ASet = ST.rec (isSetSTree' ASet) STree→STree'

∥SForest∥→SForest' : ∥ SForest A ∥₂ → SForest' A
∥SForest∥→SForest' = ST.rec trunc SForest→SForest'

module _ {A : Type ℓ} where
  open MotiveSet

  Backward : MotiveSet A _ _
  Backward .STreeᴹ = ∥ STree A ∥₂
  Backward .SForestᴹ = ∥ SForest A ∥₂
  Backward .isSetSForestᴹ = squash₂
  Backward ._▸ᴹ_ = _∣▸∣_
  Backward .[]ᴹ = ∣[]∣
  Backward ._∷ᴹ_ = _∣∷∣_
  Backward .swapᴹ = ∣swap∣

  open Rec' Backward public renaming
    (recTree' to STree'→∥STree∥; recForest' to SForest'→∥SForest∥)


module _ (ASet : isSet A) where

  ∥STree∥→STree'-arr : (ts : ∥ SForest A ∥₂) (x : A) →
    ∥STree∥→STree' ASet (ts ∣▸∣ x) ≡ (∥SForest∥→SForest' ts ▸ x)
  ∥STree∥→STree'-arr =
    ST.elim (λ _ → isProp→isSet (isPropΠ λ _ → isSetSTree' ASet _ _))
      (λ _ _ → refl)

  ∥SForest∥→SForest'-cons : (t : ∥ STree A ∥₂) (ts : ∥ SForest A ∥₂) →
    ∥SForest∥→SForest' (t ∣∷∣ ts)
      ≡ (∥STree∥→STree' ASet t ∷ ∥SForest∥→SForest' ts)
  ∥SForest∥→SForest'-cons =
    ST.elim2 (λ _ _ → isProp→isSet (trunc _ _)) (λ _ _ → refl)


module _ (ASet : isSet A) where
  open MotiveDepProp'

  Section : MotiveDepProp' A _ _
  Section .STreeᴹ t = ∥STree∥→STree' ASet (STree'→∥STree∥ t) ≡ t
  Section .SForestᴹ ts = ∥SForest∥→SForest' (SForest'→∥SForest∥ ts) ≡ ts
  Section .isPropSForestᴹ _ = trunc _ _
  Section ._▸ᴹ_ {ts} ih x =
    ∥STree∥→STree'-arr ASet (SForest'→∥SForest∥ ts) x ∙ cong (_▸ x) ih
  Section .[]ᴹ = refl
  Section ._∷ᴹ_ {t} {ts} ih1 ih2 =
    ∥SForest∥→SForest'-cons ASet (STree'→∥STree∥ t) (SForest'→∥SForest∥ ts)
      ∙ cong₂ _∷_ ih1 ih2

  open ElimProp' Section public renaming
    (elimTreeProp' to sectionTree; elimForestProp' to sectionForest)


module _ (ASet : isSet A) where
  open MotiveDepProp

  Retract : MotiveDepProp A _ _
  Retract .STreeᴹ t = STree'→∥STree∥ (STree→STree' t) ≡ ∣ t ∣₂
  Retract .SForestᴹ ts = SForest'→∥SForest∥ (SForest→SForest' ts) ≡ ∣ ts ∣₂
  Retract .isPropSForestᴹ _ = squash₂ _ _
  Retract ._▸ᴹ_ ih x = cong (_∣▸∣ x) ih
  Retract .[]ᴹ = refl
  Retract ._∷ᴹ_ ih1 ih2 = cong₂ _∣∷∣_ ih1 ih2

  open ElimProp Retract public renaming
    (elimTreeProp to retractTree'; elimForestProp to retractForest')

  retractTree : (t : ∥ STree A ∥₂) →
    STree'→∥STree∥ (∥STree∥→STree' ASet t) ≡ t
  retractTree = ST.elim (λ _ → isProp→isSet (squash₂ _ _)) retractTree'

  retractForest : (ts : ∥ SForest A ∥₂) →
    SForest'→∥SForest∥ (∥SForest∥→SForest' ts) ≡ ts
  retractForest = ST.elim (λ _ → isProp→isSet (squash₂ _ _)) retractForest'


∥STree∥IsoSTree' : isSet A → Iso (∥ STree A ∥₂) (STree' A)
∥STree∥IsoSTree' ASet =
  iso (∥STree∥→STree' ASet) STree'→∥STree∥
    (sectionTree ASet) (retractTree ASet)

∥STree∥≡STree' : isSet A → ∥ STree A ∥₂ ≡ STree' A
∥STree∥≡STree' ASet = isoToPath (∥STree∥IsoSTree' ASet)

∥SForest∥IsoSForest' : isSet A → Iso (∥ SForest A ∥₂) (SForest' A)
∥SForest∥IsoSForest' ASet =
  iso ∥SForest∥→SForest' SForest'→∥SForest∥
    (sectionForest ASet) (retractForest ASet)

∥SForest∥≡SForest' : isSet A → ∥ SForest A ∥₂ ≡ SForest' A
∥SForest∥≡SForest' ASet = isoToPath (∥SForest∥IsoSForest' ASet)

module _ (discreteA : Discrete A) where
  private
    ASet = Discrete→isSet discreteA

  discrete∥STree∥ : Discrete ∥ STree A ∥₂
  discrete∥STree∥ =
    transport (λ i → Discrete (∥STree∥≡STree' ASet (~ i)))
      (discreteSTree' discreteA)

  discrete∥SForest∥ : Discrete ∥ SForest A ∥₂
  discrete∥SForest∥ =
    transport (λ i → Discrete (∥SForest∥≡SForest' ASet (~ i)))
      (discreteSForest' discreteA)


module Test where private
  open import Cubical.Data.Nat using (discreteℕ)

  _≟_ = discrete∥SForest∥ discreteℕ

  X = ι 0
  Y = ι 1
  [X] = ι 2

  ty1 = (X ▶ Y ▶ Y) ▶ Y ▶ [X] ▶ Y
  ty2 = (X ++ Y ▶ Y) ▶ [X] ▶ Y ▶ Y
  ty3 = (Y ▶ X ▶ Y) ▶ Y ▶ [X] ▶ Y
  ty4 = (Y ▶ X ▶ Y) ▶ Y ▶ [X] ▶ X

  _ : ∣ ty1 ∣₂ ≟ ∣ ty2 ∣₂ ≡ yes _
  _ = refl

  _ : ∣ ty1 ∣₂ ≟ ∣ ty3 ∣₂ ≡ yes _
  _ = refl

  _ : ∣ ty1 ∣₂ ≟ ∣ ty4 ∣₂ ≡ no _
  _ = refl
