module SymmetricMonoidal.SymmetricList.Properties where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function using (_∘_; idfun)
open import Cubical.Foundations.GroupoidLaws using
  (cong-∙; cong-∙∙; doubleCompPath-elim; doubleCompPath-elim';
    assoc; rUnit; lUnit; symDistr)
open import Cubical.Foundations.HLevels using
  (isPropΠ; isPropΠ2; isPropΠ3; isSetΠ; isSetΠ2; isGroupoid×;
    isOfHLevelPathP'; isGroupoidRetract; isSet→isGroupoid; hProp; isSetHProp)
open import Cubical.Foundations.Path using
  (flipSquare; compPath→Square; Square→compPath)
open import Cubical.Data.Empty using (⊥; isProp⊥)
open import Cubical.Data.Fin.Recursive.Base using (Fin)
open import Cubical.Data.Fin.Recursive.Properties using (isSetFin)
open import Cubical.Data.Nat.Base using (ℕ)
open import Cubical.Data.Sigma.Base using (_×_; _,_)
open import Cubical.Data.Unit using (Unit; tt; isPropUnit)
open import Cubical.Relation.Nullary using (¬_)

open import Cubical.Foundations.Extra using
  (doubleCompPaths→Square; doubleCompPaths→Square'; Square→doubleCompPath';
    paste; pasteS; _∙h_; _∙v_; congSquare; ∙-extendL; ∙-extendR')

open import SymmetricMonoidal.SymmetricList

private
  variable
    ℓ : Level
    A B C : Type ℓ
    x y : A
    xs ys : SList A

--------------------------------------------------------------------------------
-- Basic properties

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

map-++ : (f : A → B) (xs ys : SList A) →
  map f (xs ++ ys) ≡ map f xs ++ map f ys
map-++ f =
  elimSet
    (λ _ → isSetΠ λ _ → trunc _ _)
    (λ _ → refl)
    (λ x ih ys → cong (f x ∷_) (ih ys))
    (λ x y ih j ys i → swap (f x) (f y) (ih ys i) j)

map-id : (xs : SList A) → map (idfun _) xs ≡ xs
map-id =
  elimSet
    (λ _ → trunc _ _)
    refl
    (λ x → cong (x ∷_))
    (λ x y ih j i → swap x y (ih i) j)

map-∘ : (f : B → C) (g : A → B) (xs : SList A) →
  map (f ∘ g) xs ≡ map f (map g xs)
map-∘ f g =
  elimSet
    (λ _ → trunc _ _)
    refl
    (λ x → cong (f (g x) ∷_))
    (λ x y ih j i → swap (f (g x)) (f (g y)) (ih i) j)

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
          (cong (λ zs → y ∷ z ∷ zs) p)
          (cong (λ zs → z ∷ y ∷ zs) p)
          (swap y z (x ∷ xs ++ ys))
          (swap y z (xs ++ x ∷ ys))
        filler1 = flipSquare (swap-natural y z p)

        filler2 : Path _
          ((swap x y (z ∷ xs ++ ys) ∙ cong (y ∷_) (swap x z (xs ++ ys)))
            ∙ cong (λ zs → y ∷ z ∷ zs) p)
          (swap x y (z ∷ xs ++ ys)
            ∙ cong (y ∷_) (swap x z (xs ++ ys) ∙ cong (z ∷_) p))
        filler2 = sym (cong (swap x y _ ∙_) (cong-∙ (y ∷_) _ _) ∙ assoc _ _ _)

        filler3 : Path _
          ((swap x z (y ∷ xs ++ ys) ∙ cong (z ∷_) (swap x y (xs ++ ys)))
            ∙ cong (λ zs → z ∷ y ∷ zs) p)
          (swap x z (y ∷ xs ++ ys)
            ∙ cong (z ∷_) (swap x y (xs ++ ys) ∙ cong (y ∷_) p))
        filler3 = sym (cong (swap x z _ ∙_) (cong-∙ (z ∷_) _ _) ∙ assoc _ _ _)

        goal : Square
          (swap x y (z ∷ xs ++ ys)
            ∙ cong (y ∷_) (swap x z (xs ++ ys) ∙ cong (z ∷_) p))
          (swap x z (y ∷ xs ++ ys)
            ∙ cong (z ∷_) (swap x y (xs ++ ys) ∙ cong (y ∷_) p))
          (cong (x ∷_) (swap y z (xs ++ ys)))
          (swap y z (xs ++ x ∷ ys))
        goal = pasteS filler2 filler3 refl refl (filler0 ∙h filler1)


abstract

  shift-hexagon : (x y : A) (xs ys : SList A) →
    Square
      (cong (x ∷_) (shift y xs ys) ∙ shift x xs (y ∷ ys))
      (cong (y ∷_) (shift x xs ys) ∙ shift y xs (x ∷ ys))
      (swap x y (xs ++ ys))
      (cong (xs ++_) (swap x y ys))
  shift-hexagon x y =
    elimProp
      (λ _ → isPropΠ λ _ → isOfHLevelPathP' 1 (trunc _ _) _ _)
      (λ ys →
        pasteS (lUnit refl) (lUnit refl) refl refl
          (flipSquare (refl {x = swap x y ys})))
      (λ z {xs} ih ys →
        let filler0 : Square
              (cong (x ∷_) (swap y z (xs ++ ys)) ∙ swap x z (y ∷ xs ++ ys))
              (cong (y ∷_) (swap x z (xs ++ ys)) ∙ swap y z (x ∷ xs ++ ys))
              (swap x y (z ∷ xs ++ ys))
              (cong (z ∷_) (swap x y (xs ++ ys)))
            filler0 = flipSquare (doubleCompPaths→Square' (ybe x y z (xs ++ ys)))

            filler1 : Path _
              ((cong (x ∷_) (swap y z (xs ++ ys))
                  ∙ swap x z (y ∷ xs ++ ys))
                ∙ cong (λ zs → z ∷ x ∷ zs) (shift y xs ys)
                ∙ cong (z ∷_) (shift x xs (y ∷ ys)))
              (cong (x ∷_)
                  (swap y z (xs ++ ys) ∙ cong (z ∷_) (shift y xs ys))
                ∙ swap x z (xs ++ y ∷ ys)
                ∙ cong (z ∷_) (shift x xs (y ∷ ys)))
            filler1 =
              pasteS
                (assoc _ _ _)
                (assoc _ _ _ ∙ ∙-extendL (sym (cong-∙ (x ∷_) _ _) ∙h refl))
                refl refl
                (∙-extendR'
                  (∙-extendL
                    (Square→compPath
                      (flipSquare (swap-natural x z (shift y xs ys))))))

            filler2 : Path _
              ((cong (y ∷_) (swap x z (xs ++ ys))
                  ∙ swap y z (x ∷ xs ++ ys))
                ∙ cong (λ zs → z ∷ y ∷ zs) (shift x xs ys)
                ∙ cong (z ∷_) (shift y xs (x ∷ ys)))
              (cong (y ∷_)
                  (swap x z (xs ++ ys) ∙ cong (z ∷_) (shift x xs ys))
                ∙ swap y z (xs ++ x ∷ ys)
                ∙ cong (z ∷_) (shift y xs (x ∷ ys)))
            filler2 =
              pasteS
                (assoc _ _ _)
                (assoc _ _ _ ∙ ∙-extendL (sym (cong-∙ (y ∷_) _ _) ∙h refl))
                refl refl
                (∙-extendR'
                  (∙-extendL
                    (Square→compPath
                      (flipSquare (swap-natural y z (shift x xs ys))))))

            filler3 : Square
              (cong (λ zs → z ∷ x ∷ zs) (shift y xs ys)
                ∙ cong (z ∷_) (shift x xs (y ∷ ys)))
              (cong (λ zs → z ∷ y ∷ zs) (shift x xs ys)
                ∙ cong (z ∷_) (shift y xs (x ∷ ys)))
              (cong (z ∷_) (swap x y (xs ++ ys)))
              (cong (λ zs → z ∷ xs ++ zs) (swap x y ys))
            filler3 =
              pasteS (cong-∙ (z ∷_) _ _) (cong-∙ (z ∷_) _ _) refl refl
                (congSquare (z ∷_) (ih ys))

            goal : Square
              (cong (x ∷_) (swap y z (xs ++ ys) ∙ cong (z ∷_) (shift y xs ys))
                ∙ swap x z (xs ++ y ∷ ys)
                ∙ cong (z ∷_) (shift x xs (y ∷ ys)))
              (cong (y ∷_) (swap x z (xs ++ ys) ∙ cong (z ∷_) (shift x xs ys))
                ∙ swap y z (xs ++ x ∷ ys)
                ∙ cong (z ∷_) (shift y xs (x ∷ ys)))
              (swap x y (z ∷ xs ++ ys))
              (cong (λ zs → z ∷ xs ++ zs) (swap x y ys))
            goal = pasteS filler1 filler2 refl refl (filler0 ∙h filler3)
         in goal)

--------------------------------------------------------------------------------
-- Properties of _++_

++-identityˡ : (xs : SList A) → [] ++ xs ≡ xs
++-identityˡ _ = refl

++-identityʳ : (xs : SList A) → xs ++ [] ≡ xs
++-identityʳ =
  elimSet
    (λ _ → trunc _ _)
    refl
    (λ x → cong (x ∷_))
    (λ x y ih j i → swap x y (ih i) j)

++-comm : (xs ys : SList A) → xs ++ ys ≡ ys ++ xs
++-comm =
  elimSet
    (λ _ → isSetΠ λ _ → trunc _ _)
    (λ ys → sym (++-identityʳ ys))
    (λ x {xs} ih ys → cong (x ∷_) (ih ys) ∙ shift x ys xs)
    (λ x y {xs} ih → funExt λ ys → ++-comm-swap x y xs ys (ih ys))
  where abstract
    -- this abstract speeds up type checking for ++-hexagon and ++-bigon
    ++-comm-swap : (x y : A) (xs ys : SList A) (p : xs ++ ys ≡ ys ++ xs) →
      Square
        (cong (x ∷_) (cong (y ∷_) p ∙ shift y ys xs) ∙ shift x ys (y ∷ xs))
        (cong (y ∷_) (cong (x ∷_) p ∙ shift x ys xs) ∙ shift y ys (x ∷ xs))
        (swap x y (xs ++ ys))
        (cong (ys ++_) (swap x y xs))
    ++-comm-swap x y xs ys p = goal
      where
        filler0 : Square
          (cong (λ zs → x ∷ y ∷ zs) p)
          (cong (λ zs → y ∷ x ∷ zs) p)
          (swap x y (xs ++ ys))
          (swap x y (ys ++ xs))
        filler0 = flipSquare (swap-natural x y p)

        filler1 : Square
          (cong (x ∷_) (shift y ys xs) ∙ shift x ys (y ∷ xs))
          (cong (y ∷_) (shift x ys xs) ∙ shift y ys (x ∷ xs))
          (swap x y (ys ++ xs))
          (cong (ys ++_) (swap x y xs))
        filler1 = shift-hexagon x y ys xs

        filler2 : Path _
          (cong (λ zs → x ∷ y ∷ zs) p
            ∙ cong (x ∷_) (shift y ys xs)
            ∙ shift x ys (y ∷ xs))
          (cong (x ∷_) (cong (y ∷_) p ∙ shift y ys xs) ∙ shift x ys (y ∷ xs))
        filler2 = assoc _ _ _ ∙ sym (cong (_∙ shift x ys _) (cong-∙∙ (x ∷_) _ _ _))

        filler3 : Path _
          (cong (λ zs → y ∷ x ∷ zs) p
            ∙ cong (y ∷_) (shift x ys xs)
            ∙ shift y ys (x ∷ xs))
          (cong (y ∷_) (cong (x ∷_) p ∙ shift x ys xs) ∙ shift y ys (x ∷ xs))
        filler3 = assoc _ _ _ ∙ sym (cong (_∙ shift y ys _) (cong-∙∙ (y ∷_) _ _ _))

        goal : Square
          (cong (x ∷_) (cong (y ∷_) p ∙ shift y ys xs) ∙ shift x ys (y ∷ xs))
          (cong (y ∷_) (cong (x ∷_) p ∙ shift x ys xs) ∙ shift y ys (x ∷ xs))
          (swap x y (xs ++ ys))
          (cong (ys ++_) (swap x y xs))
        goal = pasteS filler2 filler3 refl refl (filler0 ∙h filler1)

++-assoc : (xs ys zs : SList A) → (xs ++ ys) ++ zs ≡ xs ++ (ys ++ zs)
++-assoc =
  elimSet
    (λ _ → isSetΠ2 λ _ _ → trunc _ _)
    (λ _ _ → refl)
    (λ x ih ys zs → cong (x ∷_) (ih ys zs))
    (λ x y ih j ys zs i → swap x y (ih ys zs i) j)

abstract

  ++-pentagon : (xs ys zs ws : SList A) →
    Path (((xs ++ ys) ++ zs) ++ ws ≡ xs ++ (ys ++ (zs ++ ws)))
      (++-assoc (xs ++ ys) zs ws
        ∙ ++-assoc xs ys (zs ++ ws))
      (cong (_++ ws) (++-assoc xs ys zs)
        ∙∙ ++-assoc xs (ys ++ zs) ws
        ∙∙ cong (xs ++_) (++-assoc ys zs ws))
  ++-pentagon =
    elimProp
      (λ _ → isPropΠ3 λ _ _ _ → trunc _ _ _ _)
      (λ ys zs ws → sym (rUnit _) ∙ lUnit _)
      (λ x ih ys zs ws →
        sym (cong-∙ (x ∷_) _ _)
          ∙∙ cong (cong (x ∷_)) (ih ys zs ws)
          ∙∙ cong-∙∙ (x ∷_) _ _ _)

  ++-triangle : (xs ys : SList A) →
    Square
      (++-assoc xs [] ys)
      (cong (_++ ys) (++-identityʳ xs))
      refl
      (cong (xs ++_) (++-identityˡ ys))
  ++-triangle =
    elimProp
      (λ _ → isPropΠ λ _ → isOfHLevelPathP' 1 (trunc _ _) _ _)
      (λ _ → refl)
      (λ x ih ys → cong (cong (x ∷_)) (ih ys))

  -- ++-hexagon : (xs ys zs : SList A) →
  --   Path ((xs ++ ys) ++ zs ≡ ys ++ (zs ++ xs))
  --     (++-assoc xs ys zs ∙∙ ++-comm xs (ys ++ zs) ∙∙ ++-assoc ys zs xs)
  --     (cong (_++ zs) (++-comm xs ys) ∙∙ ++-assoc ys xs zs ∙∙ cong (ys ++_) (++-comm xs zs))
  -- ++-hexagon =
  --   elimProp
  --     (λ _ → isPropΠ2 λ _ _ → trunc _ _ _ _)
  --     (elimProp
  --       (λ _ → isPropΠ λ _ → trunc _ _ _ _)
  --       (λ _ → sym (rUnit _) ∙ lUnit _)
  --       (λ y ih' zs →
  --         sym (cong-∙∙ (y ∷_) _ _ _)
  --           ∙∙ cong (cong (y ∷_)) (ih' zs)
  --           ∙∙ cong-∙∙ (y ∷_) _ _ _))
  --     (λ x {xs} ih ys zs →
  --       let fill1 : Path (x ∷ (xs ++ ys) ++ zs ≡ x ∷ ys ++ zs ++ xs)
  --             (cong (x ∷_) (++-assoc xs ys zs)
  --               ∙∙ cong (x ∷_) (++-comm xs (ys ++ zs))
  --               ∙∙ cong (x ∷_) (++-assoc ys zs xs))
  --             (cong (λ ws → x ∷ ws ++ zs) (++-comm xs ys)
  --               ∙∙ cong (x ∷_) (++-assoc ys xs zs)
  --               ∙∙ cong (λ ws → x ∷ ys ++ ws) (++-comm xs zs))
  --           fill1 =
  --             sym (cong-∙∙ (x ∷_) _ _ _)
  --               ∙∙ cong (cong (x ∷_)) (ih ys zs)
  --               ∙∙ cong-∙∙ (x ∷_) _ _ _

  --           fill2 : Square
  --             (cong (x ∷_) (++-assoc ys xs zs)
  --               ∙ cong (λ ws → x ∷ ys ++ ws) (++-comm xs zs)
  --               ∙ sym (cong (x ∷_) (++-assoc ys zs xs)))
  --             (++-assoc ys (x ∷ xs) zs
  --               ∙ cong (λ ws → ys ++ x ∷ ws) (++-comm xs zs)
  --               ∙ cong (ys ++_) (shift x zs xs)
  --               ∙ sym (++-assoc ys zs (x ∷ xs)))
  --             (cong (_++ zs) (shift x ys xs))
  --             (shift x (ys ++ zs) xs)
  --           fill2 = {!   !}

  --           goal : Path (x ∷ (xs ++ ys) ++ zs ≡ ys ++ zs ++ x ∷ xs)
  --             (cong (x ∷_) (++-assoc xs ys zs)
  --               ∙∙ (cong (x ∷_) (++-comm xs (ys ++ zs)) ∙ shift x (ys ++ zs) xs)
  --               ∙∙ ++-assoc ys zs (x ∷ xs))
  --             (cong (_++ zs) (cong (x ∷_) (++-comm xs ys) ∙ shift x ys xs)
  --               ∙∙ ++-assoc ys (x ∷ xs) zs
  --               ∙∙ cong (ys ++_) (cong (x ∷_) (++-comm xs zs) ∙ shift x zs xs))
  --           goal = {!   !}
  --        in goal)

  ++-bigon : (xs ys : SList A) → ++-comm xs ys ≡ sym (++-comm ys xs)
  ++-bigon =
    elimProp
      (λ _ → isPropΠ λ _ → trunc _ _ _ _)
      (elimProp
        (λ _ → trunc _ _ _ _)
        refl
        (λ y ih → cong (cong (y ∷_)) ih ∙ rUnit _))
      (λ x {xs} ih →
        elimProp
          (λ _ → trunc _ _ _ _)
          (sym (rUnit _) ∙ cong (cong (x ∷_)) (ih []))
          (λ y {ys} ih' →
            let filler1 : Path _
                  (sym (cong (x ∷_) (cong (y ∷_) (++-comm ys xs) ∙ shift y xs ys)))
                  (cong (x ∷_) (++-comm xs (y ∷ ys)))
                filler1 = sym (congSquare (x ∷_) (ih (y ∷ ys)))

                filler2 : Square
                  (sym (cong (x ∷_) (cong (y ∷_) (++-comm ys xs) ∙ shift y xs ys)))
                  (sym (cong (x ∷_) (shift y xs ys)))
                  refl
                  (cong (λ zs → x ∷ y ∷ zs) (++-comm ys xs))
                filler2 =
                  congP (λ _ → sym)
                    (pasteS (sym (cong-∙ (x ∷_) _ _)) refl refl refl
                      (symP (compPath-filler' _ _)))

                filler3 : Path _
                  (sym (cong (λ zs → x ∷ y ∷ zs) (++-comm xs ys)))
                  (cong (λ zs → x ∷ y ∷ zs) (++-comm ys xs))
                filler3 = cong (λ p → sym (cong (λ zs → x ∷ y ∷ zs) p)) (ih ys)

                filler4 : Square
                  (swap x y (ys ++ xs))
                  (swap x y (xs ++ ys))
                  (sym (cong (λ zs → x ∷ y ∷ zs) (++-comm xs ys)))
                  (sym (cong (λ zs → y ∷ x ∷ zs) (++-comm xs ys)))
                filler4 = symP (swap-natural x y (++-comm xs ys))

                filler5 : Path _
                  (swap x y (xs ++ ys))
                  (sym (swap y x (xs ++ ys)))
                filler5 = invol x y (xs ++ ys)

                filler6 : Square
                  (cong (y ∷_) (shift x ys xs))
                  (cong (y ∷_) (cong (x ∷_) (++-comm xs ys) ∙ shift x ys xs))
                  (sym (cong (λ zs → y ∷ x ∷ zs) (++-comm xs ys)))
                  refl
                filler6 =
                  pasteS refl (sym (cong-∙ (y ∷_) _ _)) refl refl
                    (compPath-filler' _ _)

                filler7 : Path _
                  (cong (y ∷_) (cong (x ∷_) (++-comm xs ys) ∙ shift x ys xs))
                  (sym (cong (y ∷_) (++-comm ys (x ∷ xs))))
                filler7 = congSquare (y ∷_) ih'

                filler8 : Path _
                  (sym (cong (x ∷_) (shift y xs ys))
                      ∙ sym (swap y x (xs ++ ys))
                      ∙ sym (cong (y ∷_) (++-comm ys (x ∷ xs))))
                  (sym
                      (cong (y ∷_) (++-comm ys (x ∷ xs))
                        ∙ swap y x (xs ++ ys)
                        ∙ cong (x ∷_) (shift y xs ys)))
                filler8 =
                  cong (sym (cong (x ∷_) (shift y xs ys)) ∙_) (sym (symDistr _ _))
                    ∙∙ sym (symDistr _ _)
                    ∙∙ cong sym (sym (assoc _ _ _))

                goal : Square
                  (cong (x ∷_) (++-comm xs (y ∷ ys))
                    ∙ swap x y (ys ++ xs)
                    ∙ cong (y ∷_) (shift x ys xs))
                  (sym
                      (cong (y ∷_) (++-comm ys (x ∷ xs))
                        ∙ swap y x (xs ++ ys)
                        ∙ cong (x ∷_) (shift y xs ys)))
                  refl
                  refl
                goal =
                  pasteS refl filler8 refl refl
                    (pasteS filler1 refl refl refl filler2
                      ∙h pasteS refl filler5 filler3 refl filler4
                      ∙h pasteS refl filler7 refl refl filler6)
            in goal))
