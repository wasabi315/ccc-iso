module Cubical.Foundations.Extra where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Univalence
open import Cubical.Data.Sigma using (_×_; _,_; Σ-cong-equiv-snd)

private
  variable
    ℓ : Level
    A B C D : Type ℓ
    x y z w : A

--------------------------------------------------------------------------------

doubleCompPathP : {B : A → Type ℓ} →
  {s : B x} {t : B y} {u : B z} {v : B w} →
  {p : x ≡ y} {q : y ≡ z} {r : z ≡ w} →
  PathP (λ i → B (p i)) s t →
  PathP (λ i → B (q i)) t u →
  PathP (λ i → B (r i)) u v →
  PathP (λ i → B ((p ∙∙ q ∙∙ r) i)) s v
doubleCompPathP {B = B} {p = p} {q = q} {r = r} P Q R i =
  comp
    (λ j → B (doubleCompPath-filler p q r j i))
    (λ where
      j (i = i0) → P (~ j)
      j (i = i1) → R j)
    (Q i)

doubleCompPathP-filler : {B : A → Type ℓ} →
  {s : B x} {t : B y} {u : B z} {v : B w} →
  {p : x ≡ y} {q : y ≡ z} {r : z ≡ w} →
  (P : PathP (λ i → B (p i)) s t) →
  (Q : PathP (λ i → B (q i)) t u) →
  (R : PathP (λ i → B (r i)) u v) →
  SquareP
    (λ j i → B (doubleCompPath-filler p q r j i))
    Q
    (doubleCompPathP {B = B} P Q R)
    (symP P)
    R
doubleCompPathP-filler {B = B} {p = p} {q = q} {r = r} P Q R j i =
  fill
    (λ k → B (doubleCompPath-filler p q r k i))
    (λ where
      k (i = i0) → P (~ k)
      k (i = i1) → R k)
    (inS (Q i))
    j

-- doubleCompPathP agrees with _∙∙_∙∙_ on non-dependent paths
doubleCompPathP≡doubleCompPath :
  (p : Path A x y) (q : Path A y z) (r : Path A z w) →
  doubleCompPathP {p = p} {q = q} {r = r} p q r ≡ (p ∙∙ q ∙∙ r)
doubleCompPathP≡doubleCompPath {A = A} p q r j i =
  comp
    (λ _ → A)
    (λ where
      k (i = i0) → p (~ k)
      k (i = i1) → r k
      k (j = i0) → doubleCompPathP-filler {p = p} {q = q} {r = r} p q r k i
      k (j = i1) → doubleCompPath-filler p q r k i)
    (q i)

TypeOfHLevel≡≡ : (n : HLevel) {A B : TypeOfHLevel ℓ n} {p q : A ≡ B} →
  cong fst p ≡ cong fst q → p ≡ q
TypeOfHLevel≡≡ n {p = p} {q = q} P j i =
  P j i ,
  isSet→SquareP
    (λ k l → isProp→isSet (isPropIsOfHLevel {A = P k l} n))
    (cong snd p) (cong snd q)
    refl refl
    j i

uaDoubleCompEquiv : (e : A ≃ B) (f : B ≃ C) (g : C ≃ D) →
  ua (e ∙ₑ f ∙ₑ g) ≡ ua e ∙∙ ua f ∙∙ ua g
uaDoubleCompEquiv =
  EquivJ
    (λ _ e → ∀ f g → ua (e ∙ₑ f ∙ₑ g) ≡ ua e ∙∙ ua f ∙∙ ua g)
    (EquivJ
      (λ _ f → ∀ g →
        ua (idEquiv _ ∙ₑ f ∙ₑ g) ≡ ua (idEquiv _) ∙∙ ua f ∙∙ ua g)
      (λ g →
        cong ua (compEquivIdEquiv _ ∙ compEquivIdEquiv _)
          ∙∙ lUnit (ua g)
          ∙∙ sym (cong₂ (_∙∙_∙∙ ua g) uaIdEquiv uaIdEquiv)))

×-cong-equiv-snd : A ≃ B → C × A ≃ C × B
×-cong-equiv-snd e = Σ-cong-equiv-snd λ _ → e

ua×-cong-equiv-snd : (e : A ≃ B) → ua (×-cong-equiv-snd e) ≡ cong (C ×_) (ua e)
ua×-cong-equiv-snd =
  EquivJ
    (λ _ e → ua (×-cong-equiv-snd e) ≡ cong (_ ×_) (ua e))
    (cong ua (equivEq refl) ∙∙ uaIdEquiv ∙∙ cong (cong (_ ×_)) (sym uaIdEquiv))
