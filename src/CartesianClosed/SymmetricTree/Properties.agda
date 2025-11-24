module CartesianClosed.SymmetricTree.Properties where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function using (idfun; _∘_)
open import Cubical.Foundations.HLevels using (isSetΠ)
open import Cubical.Data.Unit using (Unit*; tt*)

open import CartesianClosed.SymmetricTree
import SymmetricMonoidal.SymmetricList as SList
import SymmetricMonoidal.SymmetricList.Properties as SListProps

private
  variable
    ℓ ℓ′ ℓ″ : Level
    A B C : Type ℓ

--------------------------------------------------------------------------------
-- Basic properties

open SListProps public using (swap-natural; ¬cons≡nil)

module MapAppend {A : Type ℓ} {B : Type ℓ′} (f : A → B) where
  open MotiveDepSet

  MapAppendMotive : MotiveDepSet A (ℓ-max ℓ ℓ′) (ℓ-max ℓ ℓ′)
  MapAppendMotive .STreeᴹ _ = Unit*
  MapAppendMotive .SForestᴹ ts =
    ∀ us → mapForest f (ts ++ us) ≡ mapForest f ts ++ mapForest f us
  MapAppendMotive .isSetSForestᴹ _ = isSetΠ λ _ → trunc _ _
  MapAppendMotive ._▸ᴹ_ _ _ = tt*
  MapAppendMotive .[]ᴹ _ = refl
  MapAppendMotive ._∷ᴹ_ _ ih us = cong (_ ∷_) (ih us)
  MapAppendMotive .swapᴹ {t} {u} _ _ ih j us i =
    swap (mapTree f t) (mapTree f u) (ih us i) j

  open ElimSet MapAppendMotive public using () renaming
    (elimForestSet to mapForest-++)

open MapAppend public using (mapForest-++)

module MapId {A : Type ℓ} where
  open MotiveDepSet

  MapIdMotive : MotiveDepSet A ℓ ℓ
  MapIdMotive .STreeᴹ t = mapTree (idfun _) t ≡ t
  MapIdMotive .SForestᴹ ts = mapForest (idfun _) ts ≡ ts
  MapIdMotive .isSetSForestᴹ _ = trunc _ _
  MapIdMotive ._▸ᴹ_ ih x = cong (_▸ x) ih
  MapIdMotive .[]ᴹ = refl
  MapIdMotive ._∷ᴹ_ ih1 ih2 = cong₂ _∷_ ih1 ih2
  MapIdMotive .swapᴹ ih1 ih2 ih3 j i = swap (ih1 i) (ih2 i) (ih3 i) j

  open ElimSet MapIdMotive public renaming
    (elimTreeSet to mapTree-id; elimForestSet to mapForest-id)

open MapId public using (mapTree-id; mapForest-id)

module MapComp (f : B → C) (g : A → B) where
  open MotiveDepSet

  MapCompMotive : MotiveDepSet A _ _
  MapCompMotive .STreeᴹ t = mapTree (f ∘ g) t ≡ mapTree f (mapTree g t)
  MapCompMotive .SForestᴹ ts = mapForest (f ∘ g) ts ≡ mapForest f (mapForest g ts)
  MapCompMotive .isSetSForestᴹ _ = trunc _ _
  MapCompMotive ._▸ᴹ_ ih x = cong (_▸ f (g x)) ih
  MapCompMotive .[]ᴹ = refl
  MapCompMotive ._∷ᴹ_ ih1 ih2 = cong₂ _∷_ ih1 ih2
  MapCompMotive .swapᴹ ih1 ih2 ih3 j i = swap (ih1 i) (ih2 i) (ih3 i) j

  open ElimSet MapCompMotive public renaming
    (elimTreeSet to mapTree-∘; elimForestSet to mapForest-∘)

open MapComp public using (mapTree-∘; mapForest-∘)

--------------------------------------------------------------------------------
-- Properties of _++_

open SListProps public using
 (shift; ++-identityˡ; ++-identityʳ; ++-comm; ++-assoc;
   ++-pentagon; ++-triangle; ++-bigon)

--------------------------------------------------------------------------------
-- Properties of _▶_

►-identityˡ : (t : STree A) → t ≡ ([] ► t)
►-identityˡ (ts ▸ x) = refl

▶-identityˡ : (ts : SForest A) → ts ≡ ([] ▶ ts)
▶-identityˡ =
  SList.elimSet
    (λ _ → trunc _ _)
    refl
    (λ t ih → cong₂ _∷_ (►-identityˡ t) ih)
    (λ t u ih j i → swap (►-identityˡ t i) (►-identityˡ u i) (ih i) j)

►-curry : (ts us : SForest A) (t : STree A) → (ts ► us ► t) ≡ (ts ++ us ► t)
►-curry ts us (vs ▸ x) = cong (_▸ x) (sym (++-assoc ts us vs))

▶-curry : (ts us vs : SForest A) → (ts ▶ us ▶ vs) ≡ (ts ++ us ▶ vs)
▶-curry ts us =
  SList.elimSet
    (λ _ → trunc _ _)
    refl
    (λ t ih → cong₂ _∷_ (►-curry ts us t) ih)
    (λ t u ih j i → swap (►-curry ts us t i) (►-curry ts us u i) (ih i) j)

▶-distribˡ : (ts us vs : SForest A) → (ts ▶ us ++ vs) ≡ ((ts ▶ us) ++ (ts ▶ vs))
▶-distribˡ ts = SListProps.map-++ (ts ►_)

⇒-annihilʳ : (ts : SForest A) → (ts ▶ []) ≡ []
⇒-annihilʳ _ = refl
