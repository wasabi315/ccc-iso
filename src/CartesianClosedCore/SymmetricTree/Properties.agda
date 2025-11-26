module CartesianClosedCore.SymmetricTree.Properties where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function using (idfun; _∘_)
open import Cubical.Foundations.HLevels using (isSetΠ)
open import Cubical.Data.Unit using (Unit*; tt*)

open import CartesianClosedCore.SymmetricTree
import SymmetricMonoidalGroupoid.SymmetricList as SList
import SymmetricMonoidalGroupoid.SymmetricList.Properties as SListProps

private
  variable
    ℓ ℓ′ ℓ″ : Level
    A B C : Type ℓ

--------------------------------------------------------------------------------
-- Basic properties

open SListProps public using (swap-natural; ¬cons≡nil)

mapForest-++ : (f : A → B) (ts us : SForest A) →
  mapForest f (ts ++ us) ≡ mapForest f ts ++ mapForest f us
mapForest-++ f =
  SList.elimSet
    (λ _ → isSetΠ λ _ → trunc _ _)
    (λ _ → refl)
    (λ x ih us → cong (mapTree f x ∷_) (ih us))
    (λ x y ih j us i → swap (mapTree f x) (mapTree f y) (ih us i) j)

module MapId {A : Type ℓ} where
  open MotiveDepSet

  MapId : MotiveDepSet A ℓ ℓ
  MapId .STreeᴹ t = mapTree (idfun _) t ≡ t
  MapId .SForestᴹ ts = mapForest (idfun _) ts ≡ ts
  MapId .isSetSForestᴹ _ = trunc _ _
  MapId ._▸ᴹ_ ih x = cong (_▸ x) ih
  MapId .[]ᴹ = refl
  MapId ._∷ᴹ_ ih1 ih2 = cong₂ _∷_ ih1 ih2
  MapId .swapᴹ ih1 ih2 ih3 j i = swap (ih1 i) (ih2 i) (ih3 i) j

  open ElimSet MapId public renaming
    (elimTreeSet to mapTree-id; elimForestSet to mapForest-id)

open MapId public using (mapTree-id; mapForest-id)

module MapComp (f : B → C) (g : A → B) where
  open MotiveDepSet

  MapComp : MotiveDepSet A _ _
  MapComp .STreeᴹ t = mapTree (f ∘ g) t ≡ mapTree f (mapTree g t)
  MapComp .SForestᴹ ts = mapForest (f ∘ g) ts ≡ mapForest f (mapForest g ts)
  MapComp .isSetSForestᴹ _ = trunc _ _
  MapComp ._▸ᴹ_ ih x = cong (_▸ f (g x)) ih
  MapComp .[]ᴹ = refl
  MapComp ._∷ᴹ_ ih1 ih2 = cong₂ _∷_ ih1 ih2
  MapComp .swapᴹ ih1 ih2 ih3 j i = swap (ih1 i) (ih2 i) (ih3 i) j

  open ElimSet MapComp public renaming
    (elimTreeSet to mapTree-∘; elimForestSet to mapForest-∘)

open MapComp public using (mapTree-∘; mapForest-∘)

--------------------------------------------------------------------------------
-- Properties of _++_

open SListProps public using
 (shift; ++-identityˡ; ++-identityʳ; ++-comm; ++-assoc;
   ++-pentagon; ++-triangle; ++-hexagon; ++-bigon; symmetricMonoidalGroupoid)

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

▶-annihilʳ : (ts : SForest A) → (ts ▶ []) ≡ []
▶-annihilʳ _ = refl

--------------------------------------------------------------------------------
-- Other properties

open SListProps public using (++-swap)
