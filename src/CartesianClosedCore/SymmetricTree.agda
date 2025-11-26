module CartesianClosedCore.SymmetricTree where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels using
  (isGroupoid→CubeP; isSet→SquareP; isSet→isGroupoid)

open import Cubical.Foundations.Extra using
  (doubleCompPathP; doubleCompPathP≡doubleCompPath)

import SymmetricMonoidalGroupoid.SymmetricList as SList

private
  variable
    ℓ ℓ′ ℓ″ : Level
    A : Type ℓ

infixr 4 _▸_ _►_ _▶_

--------------------------------------------------------------------------------

-- Symmetric rose trees
-- Subtrees in the same level can be swapped, but not across levels
data STree (A : Type ℓ) : Type ℓ
SForest : (A : Type ℓ) → Type ℓ

data STree A where
  _▸_ : (ts : SForest A) (x : A) → STree A

SForest A = SList.SList (STree A)

open SList using ([]; _∷_; swap; invol; ybe; trunc) public

--------------------------------------------------------------------------------
-- Eliminators

record MotiveDep (A : Type ℓ) ℓ′ ℓ″ : Type (ℓ-suc (ℓ-max ℓ (ℓ-max ℓ′ ℓ″))) where
  no-eta-equality
  infixr 4 _▸ᴹ_
  infixr 5 _∷ᴹ_
  field
    STreeᴹ : STree A → Type ℓ′
    SForestᴹ : SForest A → Type ℓ″
    isGroupoidSForestᴹ : ∀ ts → isGroupoid (SForestᴹ ts)

    _▸ᴹ_ : ∀ {ts} (tsᴹ : SForestᴹ ts) x → STreeᴹ (ts ▸ x)

    []ᴹ : SForestᴹ []
    _∷ᴹ_ : ∀ {t ts} (tᴹ : STreeᴹ t) (tsᴹ : SForestᴹ ts) → SForestᴹ (t ∷ ts)

    swapᴹ : ∀ {t u ts} tᴹ uᴹ tsᴹ →
      PathP (λ i → SForestᴹ (swap t u ts i))
        (tᴹ ∷ᴹ uᴹ ∷ᴹ tsᴹ)
        (uᴹ ∷ᴹ tᴹ ∷ᴹ tsᴹ)

    involᴹ : ∀ {t u ts} tᴹ uᴹ tsᴹ →
      SquareP (λ i j → SForestᴹ (invol t u ts i j))
        (swapᴹ tᴹ uᴹ tsᴹ)
        (symP (swapᴹ uᴹ tᴹ tsᴹ))
        refl
        refl

    ybeᴹ : ∀ {t u v ts} tᴹ uᴹ vᴹ tsᴹ →
      SquareP (λ i j → SForestᴹ (ybe t u v ts i j))
        (doubleCompPathP {B = SForestᴹ}
          (swapᴹ tᴹ uᴹ (vᴹ ∷ᴹ tsᴹ))
          (congP (λ _ → uᴹ ∷ᴹ_) (swapᴹ tᴹ vᴹ tsᴹ))
          (swapᴹ uᴹ vᴹ (tᴹ ∷ᴹ tsᴹ)))
        (doubleCompPathP {B = SForestᴹ}
          (congP (λ _ → tᴹ ∷ᴹ_) (swapᴹ uᴹ vᴹ tsᴹ))
          (swapᴹ tᴹ vᴹ (uᴹ ∷ᴹ tsᴹ))
          (congP (λ _ → vᴹ ∷ᴹ_) (swapᴹ tᴹ uᴹ tsᴹ)))
        refl
        refl


module Elim (M : MotiveDep A ℓ′ ℓ″) where
  open MotiveDep M

  elimTree : ∀ t → STreeᴹ t
  elimForest : ∀ ts → SForestᴹ ts

  elimTree (ts ▸ x) = elimForest ts ▸ᴹ x

  elimForest [] = []ᴹ
  elimForest (t ∷ ts) = elimTree t ∷ᴹ elimForest ts
  elimForest (swap t u ts i) = swapᴹ (elimTree t) (elimTree u) (elimForest ts) i
  elimForest (invol t u ts i j) =
    involᴹ (elimTree t) (elimTree u) (elimForest ts) i j
  elimForest (ybe t u v ts i j) =
    ybeᴹ (elimTree t) (elimTree u) (elimTree v) (elimForest ts) i j
  elimForest (trunc ts us p q P Q i j k) =
    isGroupoid→CubeP (λ i j k → SForestᴹ (trunc ts us p q P Q i j k))
      (λ j k → elimForest (P j k))
      (λ j k → elimForest (Q j k))
      (λ i k → elimForest (p k))
      (λ i k → elimForest (q k))
      (λ i j → elimForest ts)
      (λ i j → elimForest us)
      (isGroupoidSForestᴹ us)
      i j k


record MotiveDepSet (A : Type ℓ) ℓ′ ℓ″ : Type (ℓ-suc (ℓ-max ℓ (ℓ-max ℓ′ ℓ″))) where
  no-eta-equality
  infixr 4 _▸ᴹ_
  infixr 5 _∷ᴹ_
  field
    STreeᴹ : STree A → Type ℓ′
    SForestᴹ : SForest A → Type ℓ″
    isSetSForestᴹ : ∀ ts → isSet (SForestᴹ ts)

    _▸ᴹ_ : ∀ {ts} (tsᴹ : SForestᴹ ts) x → STreeᴹ (ts ▸ x)

    []ᴹ : SForestᴹ []
    _∷ᴹ_ : ∀ {t ts} (tᴹ : STreeᴹ t) (tsᴹ : SForestᴹ ts) → SForestᴹ (t ∷ ts)

    swapᴹ : ∀ {t u ts} tᴹ uᴹ tsᴹ →
      PathP (λ i → SForestᴹ (swap t u ts i))
        (tᴹ ∷ᴹ uᴹ ∷ᴹ tsᴹ)
        (uᴹ ∷ᴹ tᴹ ∷ᴹ tsᴹ)

  involᴹ : ∀ {t u ts} tᴹ uᴹ tsᴹ →
    SquareP (λ i j → SForestᴹ (invol t u ts i j))
      (swapᴹ tᴹ uᴹ tsᴹ)
      (symP (swapᴹ uᴹ tᴹ tsᴹ))
      refl
      refl
  involᴹ {t} {u} {ts} tᴹ uᴹ tsᴹ =
    isSet→SquareP (λ i j → isSetSForestᴹ (invol t u ts i j))
      (swapᴹ tᴹ uᴹ tsᴹ) (symP (swapᴹ uᴹ tᴹ tsᴹ)) refl refl

  ybeᴹ : ∀ {t u v ts} tᴹ uᴹ vᴹ tsᴹ →
    SquareP (λ i j → SForestᴹ (ybe t u v ts i j))
      (doubleCompPathP {B = SForestᴹ}
        (swapᴹ tᴹ uᴹ (vᴹ ∷ᴹ tsᴹ))
        (congP (λ _ → uᴹ ∷ᴹ_) (swapᴹ tᴹ vᴹ tsᴹ))
        (swapᴹ uᴹ vᴹ (tᴹ ∷ᴹ tsᴹ)))
      (doubleCompPathP {B = SForestᴹ}
        (congP (λ _ → tᴹ ∷ᴹ_) (swapᴹ uᴹ vᴹ tsᴹ))
        (swapᴹ tᴹ vᴹ (uᴹ ∷ᴹ tsᴹ))
        (congP (λ _ → vᴹ ∷ᴹ_) (swapᴹ tᴹ uᴹ tsᴹ)))
      refl
      refl
  ybeᴹ {t} {u} {v} {ts} tᴹ uᴹ vᴹ tsᴹ =
    isSet→SquareP (λ i j → isSetSForestᴹ (ybe t u v ts i j))
      (doubleCompPathP {B = SForestᴹ}
        (swapᴹ tᴹ uᴹ (vᴹ ∷ᴹ tsᴹ))
        (congP (λ _ → uᴹ ∷ᴹ_) (swapᴹ tᴹ vᴹ tsᴹ))
        (swapᴹ uᴹ vᴹ (tᴹ ∷ᴹ tsᴹ)))
      (doubleCompPathP {B = SForestᴹ}
        (congP (λ _ → tᴹ ∷ᴹ_) (swapᴹ uᴹ vᴹ tsᴹ))
        (swapᴹ tᴹ vᴹ (uᴹ ∷ᴹ tsᴹ))
        (congP (λ _ → vᴹ ∷ᴹ_) (swapᴹ tᴹ uᴹ tsᴹ)))
      refl
      refl

  motiveDep : MotiveDep A ℓ′ ℓ″
  motiveDep = record
    { STreeᴹ = STreeᴹ
    ; SForestᴹ = SForestᴹ
    ; isGroupoidSForestᴹ = λ ts → isSet→isGroupoid (isSetSForestᴹ ts)
    ; _▸ᴹ_ = _▸ᴹ_
    ; []ᴹ = []ᴹ
    ; _∷ᴹ_ = _∷ᴹ_
    ; swapᴹ = swapᴹ
    ; involᴹ = involᴹ
    ; ybeᴹ = ybeᴹ
    }


module ElimSet (M : MotiveDepSet A ℓ′ ℓ″) where
  open Elim (MotiveDepSet.motiveDep M) public renaming
    (elimTree to elimTreeSet; elimForest to elimForestSet)

record MotiveDepProp (A : Type ℓ) ℓ′ ℓ″ : Type (ℓ-suc (ℓ-max ℓ (ℓ-max ℓ′ ℓ″))) where
  no-eta-equality
  infixr 4 _▸ᴹ_
  infixr 5 _∷ᴹ_
  field
    STreeᴹ : STree A → Type ℓ′
    SForestᴹ : SForest A → Type ℓ″
    isPropSForestᴹ : ∀ ts → isProp (SForestᴹ ts)

    _▸ᴹ_ : ∀ {ts} (tsᴹ : SForestᴹ ts) x → STreeᴹ (ts ▸ x)

    []ᴹ : SForestᴹ []
    _∷ᴹ_ : ∀ {t ts} (tᴹ : STreeᴹ t) (tsᴹ : SForestᴹ ts) → SForestᴹ (t ∷ ts)

  swapᴹ : ∀ {t u ts} tᴹ uᴹ tsᴹ →
    PathP (λ i → SForestᴹ (swap t u ts i))
      (tᴹ ∷ᴹ uᴹ ∷ᴹ tsᴹ)
      (uᴹ ∷ᴹ tᴹ ∷ᴹ tsᴹ)
  swapᴹ {t} {u} {ts} _ _ _ =
    isProp→PathP (λ i → isPropSForestᴹ (swap t u ts i)) _ _

  motiveDepSet : MotiveDepSet A ℓ′ ℓ″
  motiveDepSet = record
    { STreeᴹ = STreeᴹ
    ; SForestᴹ = SForestᴹ
    ; isSetSForestᴹ = λ ts → isProp→isSet (isPropSForestᴹ ts)
    ; _▸ᴹ_ = _▸ᴹ_
    ; []ᴹ = []ᴹ
    ; _∷ᴹ_ = _∷ᴹ_
    ; swapᴹ = swapᴹ
    }


module ElimProp (M : MotiveDepProp A ℓ′ ℓ″) where
  open ElimSet (MotiveDepProp.motiveDepSet M) public renaming
    (elimTreeSet to elimTreeProp; elimForestSet to elimForestProp)


record Motive (A : Type ℓ) ℓ′ ℓ″ : Type (ℓ-suc (ℓ-max ℓ (ℓ-max ℓ′ ℓ″))) where
  no-eta-equality
  infixr 4 _▸ᴹ_
  infixr 5 _∷ᴹ_
  field
    STreeᴹ : Type ℓ′
    SForestᴹ : Type ℓ″
    isGroupoidSForestᴹ : isGroupoid SForestᴹ

    _▸ᴹ_ : SForestᴹ → A → STreeᴹ

    []ᴹ : SForestᴹ
    _∷ᴹ_ : STreeᴹ → SForestᴹ → SForestᴹ

    swapᴹ : ∀ t u ts → t ∷ᴹ u ∷ᴹ ts ≡ u ∷ᴹ t ∷ᴹ ts

    involᴹ : ∀ t u ts → swapᴹ t u ts ≡ sym (swapᴹ u t ts)

    ybeᴹ : ∀ t u v ts →
      Path (t ∷ᴹ u ∷ᴹ v ∷ᴹ ts ≡ v ∷ᴹ u ∷ᴹ t ∷ᴹ ts)
        (swapᴹ t u (v ∷ᴹ ts)
          ∙∙ cong (u ∷ᴹ_) (swapᴹ t v ts)
          ∙∙ swapᴹ u v (t ∷ᴹ ts))
        (cong (t ∷ᴹ_) (swapᴹ u v ts)
          ∙∙ swapᴹ t v (u ∷ᴹ ts)
          ∙∙ cong (v ∷ᴹ_) (swapᴹ t u ts))


module Rec (M : Motive A ℓ′ ℓ″) where
  open Motive M

  recTree : STree A → STreeᴹ
  recForest : SForest A → SForestᴹ

  recTree (ts ▸ x) = recForest ts ▸ᴹ x

  recForest [] = []ᴹ
  recForest (t ∷ ts) = recTree t ∷ᴹ recForest ts
  recForest (swap t u ts i) = swapᴹ (recTree t) (recTree u) (recForest ts) i
  recForest (invol t u ts i j) =
    involᴹ (recTree t) (recTree u) (recForest ts) i j
  recForest (ybe t u v ts i j) =
    (doubleCompPathP≡doubleCompPath _ _ _
      ∙∙ ybeᴹ (recTree t) (recTree u) (recTree v) (recForest ts)
      ∙∙ sym (doubleCompPathP≡doubleCompPath _ _ _))
    i j
  recForest (trunc ts us p q P Q i j k) =
    isGroupoidSForestᴹ
      (recForest ts) (recForest us)
      (λ i → recForest (p i)) (λ i → recForest (q i))
      (λ i j → recForest (P i j)) (λ i j → recForest (Q i j))
      i j k


record MotiveSet (A : Type ℓ) ℓ′ ℓ″ : Type (ℓ-suc (ℓ-max ℓ (ℓ-max ℓ′ ℓ″))) where
  no-eta-equality
  infixr 4 _▸ᴹ_
  infixr 5 _∷ᴹ_
  field
    STreeᴹ : Type ℓ′
    SForestᴹ : Type ℓ″
    isSetSForestᴹ : isSet SForestᴹ

    _▸ᴹ_ : SForestᴹ → A → STreeᴹ

    []ᴹ : SForestᴹ
    _∷ᴹ_ : STreeᴹ → SForestᴹ → SForestᴹ

    swapᴹ : ∀ t u ts → t ∷ᴹ u ∷ᴹ ts ≡ u ∷ᴹ t ∷ᴹ ts

  involᴹ : ∀ t u ts → swapᴹ t u ts ≡ sym (swapᴹ u t ts)
  involᴹ t u ts = isSetSForestᴹ _ _ _ _

  ybeᴹ : ∀ t u v ts →
    Path (t ∷ᴹ u ∷ᴹ v ∷ᴹ ts ≡ v ∷ᴹ u ∷ᴹ t ∷ᴹ ts)
      (swapᴹ t u (v ∷ᴹ ts)
        ∙∙ cong (u ∷ᴹ_) (swapᴹ t v ts)
        ∙∙ swapᴹ u v (t ∷ᴹ ts))
      (cong (t ∷ᴹ_) (swapᴹ u v ts)
        ∙∙ swapᴹ t v (u ∷ᴹ ts)
        ∙∙ cong (v ∷ᴹ_) (swapᴹ t u ts))
  ybeᴹ t u v ts = isSetSForestᴹ _ _ _ _

  motive : Motive A ℓ′ ℓ″
  motive = record
    { STreeᴹ = STreeᴹ
    ; SForestᴹ = SForestᴹ
    ; isGroupoidSForestᴹ = isSet→isGroupoid isSetSForestᴹ
    ; _▸ᴹ_ = _▸ᴹ_
    ; []ᴹ = []ᴹ
    ; _∷ᴹ_ = _∷ᴹ_
    ; swapᴹ = swapᴹ
    ; involᴹ = involᴹ
    ; ybeᴹ = ybeᴹ
    }


module RecSet (M : MotiveSet A ℓ′ ℓ″) where
  open Rec (MotiveSet.motive M) public renaming
    (recTree to recTreeSet; recForest to recForestSet)

--------------------------------------------------------------------------------
-- Basic operations

open SList public using ([_]; _++_)

-- ι : A → SForest A
pattern ι x = [ [] ▸ x ]

_►_ : SForest A → STree A → STree A
ts ► (us ▸ x) = ts ++ us ▸ x

_▶_ : SForest A → SForest A → SForest A
ts ▶ us = SList.map (ts ►_) us

module _ {A : Type ℓ} {B : Type ℓ′} (f : A → B) where
  open Motive

  MapMotive : Motive A ℓ′ ℓ′
  MapMotive .STreeᴹ = STree B
  MapMotive .SForestᴹ = SForest B
  MapMotive .isGroupoidSForestᴹ = trunc
  MapMotive ._▸ᴹ_ ts x = ts ▸ f x
  MapMotive .[]ᴹ = []
  MapMotive ._∷ᴹ_ = _∷_
  MapMotive .swapᴹ = swap
  MapMotive .involᴹ = invol
  MapMotive .ybeᴹ = ybe

  open Rec MapMotive renaming (recTree to mapTree; recForest to mapForest) public
