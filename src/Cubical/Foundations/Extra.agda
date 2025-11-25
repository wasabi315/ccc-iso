module Cubical.Foundations.Extra where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Foundations.Path as Path
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Univalence
open import Cubical.Data.Sigma using (_×_; _,_; Σ-cong-equiv-snd)

private
  variable
    ℓ : Level
    A B C D : Type ℓ
    x y z w : A
    p p' q q' r r' s s' t u : x ≡ y

infixr 30 _∙h_

--------------------------------------------------------------------------------
-- Combinators for composition

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

compPathP'≡compPath :
  (p : Path A x y) (q : Path A y z) →
  compPathP' {p = p} {q = q} p q ≡ (p ∙ q)
compPathP'≡compPath {A = A} {x = x} p q j i =
  comp
    (λ _ → A)
    (λ where
      k (i = i0) → x
      k (i = i1) → q k
      k (j = i0) → compPathP'-filler {p = p} {q = q} p q k i
      k (j = i1) → compPath-filler p q k i)
    (p i)

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

symDistr∙∙ : (p : x ≡ y) (q : y ≡ z) (r : z ≡ w) →
  sym (p ∙∙ q ∙∙ r) ≡ sym r ∙∙ sym q ∙∙ sym p
symDistr∙∙ p q r =
  cong sym (doubleCompPath-elim _ _ _)
    ∙ symDistr (p ∙ q) r
    ∙ cong (sym r ∙_) (symDistr p q)
    ∙ sym (doubleCompPath-elim' _ _ _)

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

--------------------------------------------------------------------------------
-- Combinators for 2-paths

paste :
  {a₀₀₀ a₀₀₁ a₀₁₀ a₀₁₁ a₁₀₀ a₁₀₁ a₁₁₀ a₁₁₁ : A} →
  {a₀₀₋ : a₀₀₀ ≡ a₀₀₁} {a₀₁₋ : a₀₁₀ ≡ a₀₁₁} {a₀₋₀ : a₀₀₀ ≡ a₀₁₀} {a₀₋₁ : a₀₀₁ ≡ a₀₁₁} →
  {a₁₀₋ : a₁₀₀ ≡ a₁₀₁} {a₁₁₋ : a₁₁₀ ≡ a₁₁₁} {a₁₋₀ : a₁₀₀ ≡ a₁₁₀} {a₁₋₁ : a₁₀₁ ≡ a₁₁₁} →
  {a₋₀₀ : a₀₀₀ ≡ a₁₀₀} {a₋₀₁ : a₀₀₁ ≡ a₁₀₁} {a₋₁₀ : a₀₁₀ ≡ a₁₁₀} {a₋₁₁ : a₀₁₁ ≡ a₁₁₁} →
  Square a₀₀₋ a₁₀₋ a₋₀₀ a₋₀₁ →
  Square a₀₁₋ a₁₁₋ a₋₁₀ a₋₁₁ →
  Square a₀₋₀ a₁₋₀ a₋₀₀ a₋₁₀ →
  Square a₀₋₁ a₁₋₁ a₋₀₁ a₋₁₁ →
  Square a₀₀₋ a₀₁₋ a₀₋₀ a₀₋₁ →
  Square a₁₀₋ a₁₁₋ a₁₋₀ a₁₋₁
paste P Q R S T j i =
  hcomp
    (λ where
      k (j = i0) → P k i
      k (j = i1) → Q k i
      k (i = i0) → R k j
      k (i = i1) → S k j)
    (T j i)

pasteS : p ≡ p' → q ≡ q' → r ≡ r' → s ≡ s' → Square p q r s → Square p' q' r' s'
pasteS = paste

-- Horizontal composition of squares
_∙h_ = _∙₂_

-- Vertical composition of squares
open Path using () renaming (_∙v_ to infixr 30 _∙v_) public

congSquare : (f : A → B) →
  Square p q r s →
  Square (cong f p) (cong f q) (cong f r) (cong f s)
congSquare f P j i = f (P j i)

∙-extendL : p ∙ q ≡ r ∙ s → p ∙ q ∙ t ≡ r ∙ s ∙ t
∙-extendL {t = t} P = (assoc _ _ _ ∙∙ cong (_∙ t) P ∙∙ sym (assoc _ _ _))

∙-extendL' : p ∙ q ≡ r ∙ s → (p ∙ q) ∙ t ≡ (r ∙ s) ∙ t
∙-extendL' {t = t} P = cong (_∙ t) P

∙-extendR : p ∙ q ≡ r ∙ s → (t ∙ p) ∙ q ≡ (t ∙ r) ∙ s
∙-extendR {t = t} P = sym (assoc _ _ _) ∙∙ cong (t ∙_) P ∙∙ assoc _ _ _

∙-extendR' : p ∙ q ≡ r ∙ s → t ∙ (p ∙ q) ≡ t ∙ (r ∙ s)
∙-extendR' {t = t} P = cong (t ∙_) P

_⟩∙⟨_ : p ≡ q → r ≡ s → p ∙ r ≡ q ∙ s
(p ⟩∙⟨ q) i = p i ∙ q i

_⟩∙∙⟨_⟩∙∙⟨_ : p ≡ q → r ≡ s → t ≡ u → (p ∙∙ r ∙∙ t) ≡ (q ∙∙ s ∙∙ u)
(p ⟩∙∙⟨ q ⟩∙∙⟨ t) i = p i ∙∙ q i ∙∙ t i

--------------------------------------------------------------------------------

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

×-cong-equiv-snd : A ≃ B → C × A ≃ C × B
×-cong-equiv-snd e = Σ-cong-equiv-snd λ _ → e

ua×-cong-equiv-snd : (e : A ≃ B) → ua (×-cong-equiv-snd e) ≡ cong (C ×_) (ua e)
ua×-cong-equiv-snd =
  EquivJ
    (λ _ e → ua (×-cong-equiv-snd e) ≡ cong (_ ×_) (ua e))
    (cong ua (equivEq refl) ∙∙ uaIdEquiv ∙∙ cong (cong (_ ×_)) (sym uaIdEquiv))
