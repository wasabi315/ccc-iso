module SymmetricMonoidal.SymmetricList.Properties where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function using (_∘_)
open import Cubical.Foundations.GroupoidLaws using
  (cong-∙; cong-∙∙; doubleCompPath-elim; doubleCompPath-elim';
    assoc; rUnit; lUnit; symDistr)
open import Cubical.Foundations.HLevels using
  (isPropΠ; isPropΠ2; isPropΠ3; isSetΠ; isSetΠ2; isGroupoid×;
    isOfHLevelPathP'; isGroupoidRetract; isSet→isGroupoid; hProp; isSetHProp)
open import Cubical.Foundations.Path using
  (flipSquare; compPath→Square; Square→compPath; _∙v_)
open import Cubical.Data.Empty using (⊥; isProp⊥)
open import Cubical.Data.Fin.Recursive.Base using (Fin)
open import Cubical.Data.Fin.Recursive.Properties using (isSetFin)
open import Cubical.Data.Nat.Base using (ℕ)
open import Cubical.Data.Sigma.Base using (_×_; _,_)
open import Cubical.Data.Unit using (Unit; tt; isPropUnit)
open import Cubical.Relation.Nullary using (¬_)

open import SymmetricMonoidal.SymmetricList

private
  variable
    ℓ : Level
    A B : Type ℓ
    x y : A
    xs ys : SList A

--------------------------------------------------------------------------------

doubleCompPaths→Square : {x y y' z z' w : A} →
  {p : x ≡ y} {q : y ≡ z} {r : z ≡ w} →
  {p' : x ≡ y'} {q' : y' ≡ z'} {r' : z' ≡ w} →
  (p ∙∙ q ∙∙ r) ≡ (p' ∙∙ q' ∙∙ r') →
  Square (p ∙ q) (q' ∙ r') p' r
doubleCompPaths→Square P =
  compPath→Square
    (sym (doubleCompPath-elim' _ _ _) ∙∙ sym P ∙∙ doubleCompPath-elim _ _ _)

doubleCompPaths→Square' : {x y y' z z' w : A} →
  {p : x ≡ y} {q : y ≡ z} {r : z ≡ w} →
  {p' : x ≡ y'} {q' : y' ≡ z'} {r' : z' ≡ w} →
  (p ∙∙ q ∙∙ r) ≡ (p' ∙∙ q' ∙∙ r') →
  Square p r' (p' ∙ q') (q ∙ r)
doubleCompPaths→Square' P =
  compPath→Square
    (sym (doubleCompPath-elim _ _ _) ∙∙ sym P ∙∙ doubleCompPath-elim' _ _ _)

Square→doubleCompPath' : {x y y' z z' w : A} →
  {p : x ≡ y} {q : y ≡ z} {r : z ≡ w} →
  {p' : x ≡ y'} {q' : y' ≡ z'} {r' : z' ≡ w} →
  Square p r' (p' ∙ q') (q ∙ r) →
  (p ∙∙ q ∙∙ r) ≡ (p' ∙∙ q' ∙∙ r')
Square→doubleCompPath' P =
  doubleCompPath-elim' _ _ _
    ∙∙ sym (Square→compPath P)
    ∙∙ sym (doubleCompPath-elim _ _ _)

doubleRUnit : {x y : A} (p : x ≡ y) → p ≡ (p ∙∙ refl ∙∙ refl)
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

--------------------------------------------------------------------------------

¬cons≡nil : ¬ x ∷ xs ≡ []
¬cons≡nil p = subst (fst ∘ f) p tt
  where
    f : SList A → hProp ℓ-zero
    f =
      elimSet
        (λ _ → isSetHProp)
        (⊥ , isProp⊥)
        (λ _ _ → Unit , isPropUnit)
        (λ _ _ _ → refl)

swap-natural : (x y : A) (p : xs ≡ ys) →
  Square
    (swap x y xs)
    (swap x y ys)
    (cong (λ zs → x ∷ y ∷ zs) p)
    (cong (λ zs → y ∷ x ∷ zs) p)
swap-natural x y =
  J (λ zs p →
      Square
        (swap x y _)
        (swap x y zs)
        (cong (λ zs → x ∷ y ∷ zs) p)
        (cong (λ zs → y ∷ x ∷ zs) p))
    refl

--------------------------------------------------------------------------------
-- Important property

shift : (x : A) (xs ys : SList A) → x ∷ xs ++ ys ≡ xs ++ x ∷ ys
shift x =
  elimSet
    (λ _ → isSetΠ λ _ → trunc _ _)
    (λ _ → refl)
    (λ y {xs} ih ys → swap x y (xs ++ ys) ∙ cong (y ∷_) (ih ys))
    (λ y z {xs} ih i ys → shift-swap y z xs ys (ih ys) i)
  module Shift where abstract

    shift-swap : ∀ y z xs ys (p : x ∷ xs ++ ys ≡ xs ++ x ∷ ys) →
      Square
        (swap x y (z ∷ xs ++ ys)
          ∙ cong (y ∷_) (swap x z (xs ++ ys) ∙ cong (z ∷_) p))
        (swap x z (y ∷ xs ++ ys)
          ∙ cong (z ∷_) (swap x y (xs ++ ys) ∙ cong (y ∷_) p))
        (cong (x ∷_) (swap y z (xs ++ ys)))
        (swap y z (xs ++ x ∷ ys))
    shift-swap y z xs ys p = goal
      where
        filler0 : Square
          (swap x y (z ∷ xs ++ ys) ∙ cong (y ∷_) (swap x z (xs ++ ys)))
          (swap x z (y ∷ xs ++ ys) ∙ cong (z ∷_) (swap x y (xs ++ ys)))
          (cong (x ∷_) (swap y z (xs ++ ys)))
          (swap y z (x ∷ xs ++ ys))
        filler0 = doubleCompPaths→Square (ybe x y z (xs ++ ys))

        filler1 : Square
          (cong (λ γ → y ∷ z ∷ γ) p)
          (cong (λ γ → z ∷ y ∷ γ) p)
          (swap y z (x ∷ xs ++ ys))
          (swap y z (xs ++ x ∷ ys))
        filler1 = flipSquare (swap-natural y z p)

        filler2 : Square
          (swap x y (z ∷ xs ++ ys)
            ∙ cong (y ∷_) (swap x z (xs ++ ys) ∙ cong (z ∷_) p))
          ((swap x y (z ∷ xs ++ ys) ∙ cong (y ∷_) (swap x z (xs ++ ys)))
            ∙ cong (λ γ → y ∷ z ∷ γ) p)
          refl
          refl
        filler2 = cong (swap x y _ ∙_) (cong-∙ (y ∷_) _ _) ∙ assoc _ _ _

        filler3 : Square
          ((swap x z (y ∷ xs ++ ys) ∙ cong (z ∷_) (swap x y (xs ++ ys)))
            ∙ cong (λ γ → z ∷ y ∷ γ) p)
          (swap x z (y ∷ xs ++ ys)
            ∙ cong (z ∷_) (swap x y (xs ++ ys) ∙ cong (y ∷_) p))
          refl
          refl
        filler3 = sym (cong (swap x z _ ∙_) (cong-∙ (z ∷_) _ _) ∙ assoc _ _ _)

        goal : Square
          (swap x y (z ∷ xs ++ ys)
            ∙ cong (y ∷_) (swap x z (xs ++ ys) ∙ cong (z ∷_) p))
          (swap x z (y ∷ xs ++ ys)
            ∙ cong (z ∷_) (swap x y (xs ++ ys) ∙ cong (y ∷_) p))
          (cong (x ∷_) (swap y z (xs ++ ys)))
          (swap y z (xs ++ x ∷ ys))
        goal = filler2 ◁ (filler0 ∙₂ filler1) ▷ filler3
