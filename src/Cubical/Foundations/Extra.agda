module Cubical.Foundations.Extra where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Foundations.Path
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

doubleCompPaths→Square : {x y y' z z' w : A} →
  {p : x ≡ y} {q : y ≡ z} {r : z ≡ w} →
  {p' : x ≡ y'} {q' : y' ≡ z'} {r' : z' ≡ w} →
  (p ∙∙ q ∙∙ r) ≡ (p' ∙∙ q' ∙∙ r') →
  Square (p ∙ q) (q' ∙ r') p' r
doubleCompPaths→Square P =
  compPath→Square
    (sym (doubleCompPath-elim' _ _ _) ∙∙ sym P ∙∙ doubleCompPath-elim _ _ _)

doubleCompPaths→Square' : ∀ {a} {A : Type a} {x y y' z z' w : A} →
  {p : x ≡ y} {q : y ≡ z} {r : z ≡ w} →
  {p' : x ≡ y'} {q' : y' ≡ z'} {r' : z' ≡ w} →
  (p ∙∙ q ∙∙ r) ≡ (p' ∙∙ q' ∙∙ r') →
  Square p r' (p' ∙ q') (q ∙ r)
doubleCompPaths→Square' P =
  compPath→Square
    (sym (doubleCompPath-elim _ _ _) ∙∙ sym P ∙∙ doubleCompPath-elim' _ _ _)

Square→doubleCompPath' : ∀ {a} {A : Type a} {x y y' z z' w : A} →
  {p : x ≡ y} {q : y ≡ z} {r : z ≡ w} →
  {p' : x ≡ y'} {q' : y' ≡ z'} {r' : z' ≡ w} →
  Square p r' (p' ∙ q') (q ∙ r) →
  (p ∙∙ q ∙∙ r) ≡ (p' ∙∙ q' ∙∙ r')
Square→doubleCompPath' P =
  doubleCompPath-elim' _ _ _
    ∙∙ sym (Square→compPath P)
    ∙∙ sym (doubleCompPath-elim _ _ _)

doubleRUnit : ∀ {a} {A : Type a} {x y : A} (p : x ≡ y) → p ≡ (p ∙∙ refl ∙∙ refl)
doubleRUnit p = rUnit _ ∙∙ rUnit _ ∙∙ sym (doubleCompPath-elim _ _ _)

_◁v_▷_ : ∀ {a} {A : Type a} {x y y' z : A} →
  {p : x ≡ y} {p' p'' : x ≡ y'} {q q' : y ≡ z} {q'' : y' ≡ z} →
  (Q : p' ≡ p'') (P : Square p q'' p' q) (R : q ≡ q') →
  Square p q'' p'' q'
Q ◁v P ▷ R = subst2 (Square _ _) Q R P

cong₂-∙ : ∀ {a b c} {A : Type a} {B : Type b} {C : Type c} →
  {x y z : A} {u v w : B} (f : A → B → C) →
  (p : x ≡ y) (q : y ≡ z) (r : u ≡ v) (s : v ≡ w) →
  cong₂ f (p ∙ q) (r ∙ s) ≡ cong₂ f p r ∙ cong₂ f q s
cong₂-∙ {x = x} {u = u} f p q r s j i =
  hcomp
    (λ where
      k (i = i0) → f x u
      k (i = i1) → f (q k) (s k)
      k (j = i0) → f (compPath-filler p q k i) (compPath-filler r s k i)
      k (j = i1) → compPath-filler (cong₂ f p r) (cong₂ f q s) k i)
    (f (p i) (r i))

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
