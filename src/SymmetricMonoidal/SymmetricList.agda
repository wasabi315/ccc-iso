module SymmetricMonoidal.SymmetricList where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels using
  (isGroupoid→CubeP; isSet→SquareP; isSet→isGroupoid)

open import Cubical.Foundations.Extra using
  (doubleCompPathP; doubleCompPathP≡doubleCompPath)

private
  variable
    ℓ : Level
    A : Type ℓ

infixr 5 _∷_ _++_

--------------------------------------------------------------------------------
-- "Normal form" of free symmetric monoidal groupoid

-- Symmetric lists
data SList (A : Type ℓ) : Type ℓ where
  [] : SList A
  _∷_ : (x : A) (xs : SList A) → SList A

  swap : ∀ x y xs → x ∷ y ∷ xs ≡ y ∷ x ∷ xs

  invol : ∀ x y xs → swap x y xs ≡ sym (swap y x xs)

  -- Yang-Baxter Equation
  ybe : ∀ x y z xs →
    Path (x ∷ y ∷ z ∷ xs ≡ z ∷ y ∷ x ∷ xs)
      (swap x y (z ∷ xs)
        ∙∙ cong (y ∷_) (swap x z xs)
        ∙∙ swap y z (x ∷ xs))
      (cong (x ∷_) (swap y z xs)
        ∙∙ swap x z (y ∷ xs)
        ∙∙ cong (z ∷_) (swap x y xs))

  trunc : ∀ xs ys (p q : xs ≡ ys) (P Q : p ≡ q) → P ≡ Q

--------------------------------------------------------------------------------
-- Eliminators

module _ {B : SList A → Type ℓ}
  (trunc* : ∀ xs → isGroupoid (B xs))
  ([]* : B [])
  (_∷*_ : ∀ x {xs} → B xs → B (x ∷ xs))
  (swap* : ∀ x y {xs} (xs* : B xs) →
    PathP (λ i → B (swap x y xs i)) (x ∷* (y ∷* xs*)) (y ∷* (x ∷* xs*)))
  (invol* : ∀ x y {xs} (xs* : B xs) →
    SquareP
      (λ i j → B (invol x y xs i j))
      (swap* x y xs*)
      (symP (swap* y x xs*))
      refl
      refl)
  (ybe* : ∀ x y z {xs} (xs* : B xs) →
    SquareP
      (λ i j → B (ybe x y z xs i j))
      (doubleCompPathP {B = B}
        (swap* x y (z ∷* xs*))
        (congP (λ _ → y ∷*_) (swap* x z xs*))
        (swap* y z (x ∷* xs*)))
      (doubleCompPathP {B = B}
        (congP (λ _ → x ∷*_) (swap* y z xs*))
        (swap* x z (y ∷* xs*))
        (congP (λ _ → z ∷*_) (swap* x y xs*)))
      refl
      refl)
  where

  elim : ∀ xs → B xs
  elim [] = []*
  elim (x ∷ xs) = x ∷* elim xs
  elim (swap x y xs i) = swap* x y (elim xs) i
  elim (invol x y xs i j) = invol* x y (elim xs) i j
  elim (ybe x y z xs i j) = ybe* x y z (elim xs) i j
  elim (trunc xs ys p q P Q i j k) =
    isGroupoid→CubeP (λ i j k → B (trunc xs ys p q P Q i j k))
      (λ j k → elim (P j k))
      (λ j k → elim (Q j k))
      (λ i k → elim (p k))
      (λ i k → elim (q k))
      (λ i j → elim xs)
      (λ i j → elim ys)
      (trunc* ys)
      i j k


module _ {B : SList A → Type ℓ}
  (trunc* : ∀ xs → isSet (B xs))
  ([]* : B [])
  (_∷*_ : ∀ x {xs} → B xs → B (x ∷ xs))
  (swap* : ∀ x y {xs} (xs* : B xs) →
    PathP (λ i → B (swap x y xs i)) (x ∷* (y ∷* xs*)) (y ∷* (x ∷* xs*)))
  where

  -- Could have been defined using elim but this is more efficient
  -- This function will be a hot-path as we often want to establish
  -- paths between SLists
  elimSet : ∀ xs → B xs
  elimSet [] = []*
  elimSet (x ∷ xs) = x ∷* elimSet xs
  elimSet (swap x y xs i) = swap* x y (elimSet xs) i
  elimSet (invol x y xs i j) =
    isSet→SquareP (λ i j → trunc* (invol x y xs i j))
      (swap* x y (elimSet xs))
      (symP (swap* y x (elimSet xs)))
      refl
      refl
      i j
  elimSet (ybe x y z xs i j) =
    isSet→SquareP (λ i j → trunc* (ybe x y z xs i j))
      (doubleCompPathP {B = B}
        (swap* x y (z ∷* elimSet xs))
        (congP (λ _ → y ∷*_) (swap* x z (elimSet xs)))
        (swap* y z (x ∷* elimSet xs)))
      (doubleCompPathP {B = B}
        (congP (λ _ → x ∷*_) (swap* y z (elimSet xs)))
        (swap* x z (y ∷* elimSet xs))
        (congP (λ _ → z ∷*_) (swap* x y (elimSet xs))))
      refl
      refl
      i j
  elimSet (trunc xs ys p q P Q i j k) =
    isGroupoid→CubeP (λ i j k → B (trunc xs ys p q P Q i j k))
      (λ j k → elimSet (P j k))
      (λ j k → elimSet (Q j k))
      (λ i k → elimSet (p k))
      (λ i k → elimSet (q k))
      (λ i j → elimSet xs)
      (λ i j → elimSet ys)
      (isSet→isGroupoid (trunc* ys))
      i j k


module _ {B : SList A → Type ℓ}
  (trunc* : ∀ xs → isProp (B xs))
  ([]* : B [])
  (_∷*_ : ∀ x {xs} → B xs → B (x ∷ xs))
  where

  elimProp : ∀ xs → B xs
  elimProp =
    elimSet
      (λ xs → isProp→isSet (trunc* xs))
      []* _∷*_
      (λ x y {xs} xs* → isProp→PathP (λ i → trunc* (swap x y xs i)) _ _)


module _ {B : Type ℓ}
  (trunc* : isGroupoid B)
  ([]* : B)
  (_∷*_ : A → B → B)
  (swap* : ∀ x y xs* → x ∷* (y ∷* xs*) ≡ y ∷* (x ∷* xs*))
  (invol* : ∀ x y xs* → swap* x y xs* ≡ sym (swap* y x xs*))
  (ybe* : ∀ x y z xs* →
    Path (x ∷* (y ∷* (z ∷* xs*)) ≡ z ∷* (y ∷* (x ∷* xs*)))
      (swap* x y (z ∷* xs*)
        ∙∙ cong (y ∷*_) (swap* x z xs*)
        ∙∙ swap* y z (x ∷* xs*))
      (cong (x ∷*_) (swap* y z xs*)
        ∙∙ swap* x z (y ∷* xs*)
        ∙∙ cong (z ∷*_) (swap* x y xs*)))
  where

  -- Could have been defined using elim but this is more efficient
  -- _++_ uses this function so it is a hot-path
  rec : SList A → B
  rec [] = []*
  rec (x ∷ xs) = x ∷* rec xs
  rec (swap x y xs i) = swap* x y (rec xs) i
  rec (invol x y xs i j) = invol* x y (rec xs) i j
  rec (ybe x y z xs i j) =
    (doubleCompPathP≡doubleCompPath _ _ _
      ∙∙ ybe* x y z (rec xs)
      ∙∙ sym (doubleCompPathP≡doubleCompPath _ _ _))
      i j
  rec (trunc xs ys p q P Q i j k) =
    trunc*
      (rec xs) (rec ys)
      (λ i → rec (p i)) (λ i → rec (q i))
      (λ i j → rec (P i j)) (λ i j → rec (Q i j))
      i j k


module _ {B : Type ℓ}
  (trunc* : isSet B)
  ([]* : B)
  (_∷*_ : A → B → B)
  (swap* : ∀ x y xs* → x ∷* (y ∷* xs*) ≡ y ∷* (x ∷* xs*))
  where

  recSet : SList A → B
  recSet =
    rec (isSet→isGroupoid trunc*) []* _∷*_ swap*
      (λ _ _ _ → trunc* _ _ _ _)
      (λ _ _ _ _ → trunc* _ _ _ _)

--------------------------------------------------------------------------------
-- Basic operations

pattern [_] x = x ∷ []

_++_ : SList A → SList A → SList A
xs ++ ys = rec trunc ys _∷_ swap invol ybe xs
