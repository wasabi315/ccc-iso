module Cubical.Foundations.Extra where

open import Cubical.Foundations.Prelude

private
  variable
    ℓ : Level
    A : Type ℓ
    B : A → Type ℓ
    x y z w : A

--------------------------------------------------------------------------------

doubleCompPathP :
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
