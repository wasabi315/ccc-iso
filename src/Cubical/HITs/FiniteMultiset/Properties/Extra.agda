module Cubical.HITs.FiniteMultiset.Properties.Extra where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function using (_∘_)
open import Cubical.Foundations.HLevels using (isProp→; isPropΠ2; isPropΠ; hProp; isSetHProp)
open import Cubical.Foundations.Isomorphism using
  (Iso; iso; isoToEquiv; isoToPath; transportIsoToPath; transportIsoToPath⁻)
open import Cubical.Foundations.Univalence using (ua; uaβ; ~uaβ)
open import Cubical.Data.Empty as ⊥ using (⊥*; ⊥; isProp⊥)
open import Cubical.Data.List as List using (List; []; _∷_; _++_; module ListPath)
open import Cubical.Data.Sigma using (Σ-syntax; ∃-syntax; _×_; _,_)
open import Cubical.Data.Sum using (_⊎_; inl; inr)
open import Cubical.Data.Unit using (Unit*; tt*; Unit; tt; isPropUnit)
open import Cubical.HITs.FiniteMultiset as FMSet using (FMSet; []; _∷_; comm; trunc)
open import Cubical.HITs.PropositionalTruncation as PT using (∥_∥₁; ∣_∣₁; squash₁)
open import Cubical.HITs.PropositionalTruncation.Monad as PTMonad
open import Cubical.HITs.SetQuotients as SQ using (_/_; [_]; eq/; squash/)
open import Cubical.Relation.Binary using (module BinaryRelation)
open import Cubical.Relation.Nullary using
  (¬_; Dec; yes; no; isPropDec; Discrete; mapDec; decRec)

open BinaryRelation
open Iso

private
  variable
    ℓ : Level
    A : Type ℓ

infix  4 _∣↭∣_
infixr 5 _∷↭_

--------------------------------------------------------------------------------

¬cons≡nil : {x : A} {xs : FMSet A} → ¬ x ∷ xs ≡ []
¬cons≡nil p = subst (fst ∘ f) p tt
  where
    f : FMSet A → hProp ℓ-zero
    f =
      FMSet.Elim.f
        (⊥ , isProp⊥) (λ _ _ → Unit , isPropUnit)
        (λ _ _ _ → refl) (λ _ → isSetHProp)

--------------------------------------------------------------------------------
-- Properties that seems to be only proved via List / _↭_

-- Permutation relation
-- Ref: https://github.com/agda/agda-stdlib/blob/master/src/Data/List/Relation/Binary/Permutation/Setoid/Properties.agda
module _ {A : Type ℓ} where
  infix  4 _↭_ _↭′_ _↭″_
  infixr 5 _↭-∷_

  data _↭_ (xs ys : List A) : Type ℓ
  _↭′_ _↭″_ : List A → List A → Type ℓ
  Comm : A → A → List A → List A → Type ℓ

  data _↭_ xs ys where
    con : xs ↭′ ys → xs ↭ ys

  xs ↭′ ys = (xs ↭″ ys) ⊎ (Σ[ zs ∈ _ ] (xs ↭ zs) × (zs ↭ ys))

  [] ↭″ [] = Unit*
  [] ↭″ y ∷ ys = ⊥*
  x ∷ xs ↭″ [] = ⊥*
  x ∷ xs ↭″ y ∷ ys = ((x ≡ y) × (xs ↭ ys)) ⊎ Comm x y xs ys

  Comm x y [] _ = ⊥*
  Comm x y (x' ∷ xs) [] = ⊥*
  Comm x y (x' ∷ xs) (y' ∷ ys) = (x ≡ y') × (x' ≡ y) × (xs ↭ ys)

  pattern ↭-[] = con (inl tt*)
  pattern _↭-∷_ p q = con (inl (inl (p , q)))
  pattern ↭-trans {zs} p q = con (inr (zs , p , q))
  pattern ↭-comm p q r = con (inl (inr (p , q , r)))

  _ : [] ↭ []
  _ = ↭-[]

  _ : ∀ {x y xs ys} → x ≡ y → xs ↭ ys → x ∷ xs ↭ y ∷ ys
  _ = _↭-∷_

  _ : ∀ {xs ys zs} → xs ↭ ys → ys ↭ zs → xs ↭ zs
  _ = ↭-trans

  _ : ∀ {x x' y y' xs ys} →
    x ≡ y' →
    x' ≡ y →
    xs ↭ ys →
    x ∷ x' ∷ xs ↭ y ∷ y' ∷ ys
  _ = ↭-comm

  ↭-refl : ∀ {xs} → xs ↭ xs
  ↭-refl {xs = []} = ↭-[]
  ↭-refl {xs = x ∷ xs} = refl ↭-∷ ↭-refl

  ↭-reflexive : ∀ {xs ys} → ListPath.Cover xs ys → xs ↭ ys
  ↭-reflexive p = subst (_ ↭_) (ListPath.decode _ _ p) ↭-refl

  ↭-sym : ∀ {xs ys} → xs ↭ ys → ys ↭ xs
  ↭-sym (↭-trans p q) = ↭-trans (↭-sym q) (↭-sym p)
  ↭-sym {xs = []} {ys = []} ↭-[] = ↭-[]
  ↭-sym {xs = x ∷ xs} {ys = y ∷ ys} (p ↭-∷ q) = sym p ↭-∷ ↭-sym q
  ↭-sym {xs = x ∷ x' ∷ xs} {ys = y ∷ y' ∷ ys} (↭-comm p q r) =
    ↭-comm (sym q) (sym p) (↭-sym r)

  ↭-shift : ∀ {x y} → x ≡ y → ∀ xs ys → x ∷ xs ++ ys ↭ xs ++ y ∷ ys
  ↭-shift p [] ys = p ↭-∷ ↭-refl
  ↭-shift p (x ∷ xs) ys =
    ↭-trans (↭-comm refl refl ↭-refl) (refl ↭-∷ ↭-shift p xs ys)

  ↭-split-helper : ∀ {x} xs ys as bs →
    xs ↭ ys →
    ListPath.Cover ys (as ++ x ∷ bs) →
    Σ[ ps ∈ _ ] Σ[ qs ∈ _ ]
      ListPath.Cover xs (ps ++ x ∷ qs) × (ps ++ qs ↭ as ++ bs)
  ↭-split-helper xs ys as bs (↭-trans p q) eq
    using ps , qs , eq' , r ← ↭-split-helper _ ys as bs q eq
    using ps' , qs' , eq'' , s ← ↭-split-helper xs _ ps qs p eq'
    = ps' , qs' , eq'' , ↭-trans s r
  ↭-split-helper [] [] [] bs ↭-[] ()
  ↭-split-helper [] [] (_ ∷ _) bs ↭-[] ()
  ↭-split-helper (x ∷ xs) (y ∷ ys) [] bs (p ↭-∷ q) (eq , eq') =
    [] , xs ,
    (p ∙ eq , ListPath.reflCode xs) ,
    ↭-trans q (↭-reflexive eq')
  ↭-split-helper (x ∷ xs) (y ∷ ys) (a ∷ as) bs (p ↭-∷ q) (eq , eq')
    using ps , qs , eq' , r ← ↭-split-helper xs ys as bs q eq'
    = a ∷ ps , qs , (p ∙ eq , eq') , refl ↭-∷ r
  ↭-split-helper (x ∷ y ∷ xs) (x' ∷ y' ∷ xs') [] (b ∷ _) (↭-comm p q r) (eq , eq' , eq'') =
    b ∷ [] , xs ,
    (p ∙ eq' , q ∙ eq , ListPath.reflCode xs) ,
    refl ↭-∷ ↭-trans r (↭-reflexive eq'')
  ↭-split-helper (x ∷ y ∷ xs) (x' ∷ y' ∷ xs') (a ∷ []) bs (↭-comm p q r) (eq , eq' , eq'') =
    [] , a ∷ xs ,
    (p ∙ eq' , q ∙ eq , ListPath.reflCode xs) ,
    refl ↭-∷ ↭-trans r (↭-reflexive eq'')
  ↭-split-helper (x ∷ y ∷ xs) (x' ∷ y' ∷ xs') (a ∷ b ∷ as) bs (↭-comm p q r) (eq , eq' , eq'')
    using ps , qs , eq''' , s ← ↭-split-helper xs xs' as bs r eq''
    = b ∷ a ∷ ps , qs ,
      (p ∙ eq' , q ∙ eq , eq''') ,
      ↭-comm refl refl s

  ↭-split : ∀ {x xs ys zs} → xs ↭ (ys ++ x ∷ zs) →
    Σ[ ps ∈ _ ] Σ[ qs ∈ _ ]
      ListPath.Cover xs (ps ++ x ∷ qs) × (ps ++ qs ↭ ys ++ zs)
  ↭-split {x = x} {xs = xs} {ys = ys} {zs = zs} p =
    ↭-split-helper xs (ys ++ x ∷ zs) ys zs p (ListPath.reflCode _)

  ↭-dropMiddleElement-Cover : ∀ {x} ws xs {ys zs} →
    ListPath.Cover (ws ++ x ∷ ys) (xs ++ x ∷ zs) →
    ws ++ ys ↭ xs ++ zs
  ↭-dropMiddleElement-Cover [] [] (_ , eq) = ↭-reflexive eq
  ↭-dropMiddleElement-Cover [] (x ∷ xs) (eq , eq') =
    ↭-trans (↭-reflexive eq') (↭-sym (↭-shift (sym eq) xs _))
  ↭-dropMiddleElement-Cover (w ∷ ws) [] (eq , eq') =
    ↭-trans (↭-shift eq ws _) (↭-reflexive eq')
  ↭-dropMiddleElement-Cover (w ∷ ws) (x ∷ xs) (eq , eq') =
    eq ↭-∷ ↭-dropMiddleElement-Cover ws xs eq'

  ↭-dropMiddleElement : ∀ {x} ws xs {ys zs} →
    ws ++ x ∷ ys ↭ xs ++ x ∷ zs →
    ws ++ ys ↭ xs ++ zs
  ↭-dropMiddleElement ws xs p
    using ps , qs , eq , q ← ↭-split p
    = ↭-trans (↭-dropMiddleElement-Cover ws ps eq) q

  ↭-drop-∷ : ∀ {x xs ys} → x ∷ xs ↭ x ∷ ys → xs ↭ ys
  ↭-drop-∷ = ↭-dropMiddleElement [] []

  ↭-differentHead : ∀ {x y xs ys} →
    ¬ x ≡ y →
    x ∷ xs ↭ y ∷ ys →
    Σ[ zs ∈ _ ] (xs ↭ y ∷ zs) × (x ∷ zs ↭ ys)
  ↭-differentHead {x} {y} {xs} {ys} neq p with ↭-split {y} {x ∷ xs} {[]} {ys} p
  ... | [] , qs , (eq , eq') , q = ⊥.rec (neq eq)
  ... | p ∷ ps , qs , (eq , eq') , q =
          ps ++ qs ,
          ↭-trans (↭-reflexive eq') (↭-sym (↭-shift refl ps qs)) ,
          subst (λ y → y ∷ ps ++ qs ↭ ys) (sym eq) q

-- Quotient of lists up to permutation

_∣↭∣_ : {A : Type ℓ} → List A → List A → Type ℓ
xs ∣↭∣ ys = ∥ xs ↭ ys ∥₁

isPropValued∣↭∣ : isPropValued (_∣↭∣_ {A = A})
isPropValued∣↭∣ _ _ = squash₁

isEquivRel∣↭∣ : isEquivRel (_∣↭∣_ {A = A})
isEquivRel∣↭∣ .isEquivRel.reflexive x = ∣ ↭-refl ∣₁
isEquivRel∣↭∣ .isEquivRel.symmetric _ _ = PT.map ↭-sym
isEquivRel∣↭∣ .isEquivRel.transitive _ _ _ = PT.map2 ↭-trans

List↭ : Type ℓ → Type ℓ
List↭ A = List A / _∣↭∣_

pattern []↭ = [ [] ]

_ : List↭ A
_ = []↭

_∷↭_ : A → List↭ A → List↭ A
_∷↭_ x =
  SQ.rec
    squash/
    (λ xs → [ x ∷ xs ])
    (λ _ _ → eq/ _ _ ∘ PT.map (refl ↭-∷_))

comm↭ : (x y : A) (xs : List↭ A) → x ∷↭ y ∷↭ xs ≡ y ∷↭ x ∷↭ xs
comm↭ x y =
  SQ.elimProp
    (λ _ → squash/ _ _)
    (λ _ → eq/ _ _ ∣ ↭-comm refl refl ↭-refl ∣₁)

reify↭ : {xs ys : List A} → [ xs ] ≡ [ ys ] → xs ∣↭∣ ys
reify↭ = SQ.effective (λ _ _ → squash₁) isEquivRel∣↭∣ _ _

drop-∷↭ : (x : A) (xs ys : List↭ A) → x ∷↭ xs ≡ x ∷↭ ys → xs ≡ ys
drop-∷↭ x =
  SQ.elimProp2
    (λ _ _ → isProp→ (squash/ _ _))
    (λ _ _ → PT.rec (squash/ _ _) (eq/ _ _ ∘ ∣_∣₁ ∘ ↭-drop-∷) ∘ reify↭)

differentHead↭ : (x y : A) (xs ys : List↭ A) →
  ¬ x ≡ y →
  x ∷↭ xs ≡ y ∷↭ ys →
  ∃[ zs ∈ _ ] (xs ≡ y ∷↭ zs) × (x ∷↭ zs ≡ ys)
differentHead↭ x y =
  SQ.elimProp2
    (λ _ _ → isPropΠ2 λ _ _ → squash₁)
    (λ xs ys neq →
      PT.map
        (λ p →
          let zs , q , r = ↭-differentHead neq p
           in [ zs ] , eq/ _ _ ∣ q ∣₁ , eq/ _ _ ∣ r ∣₁)
        ∘ reify↭)

-- Isomorphism between FMSet A and List↭ A

FMSet→List↭ : FMSet A → List↭ A
FMSet→List↭ = FMSet.Rec.f squash/ []↭ _∷↭_ comm↭

List→FMSet : List A → FMSet A
List→FMSet = List.foldr _∷_ []

perm→FMSetPath' : {xs ys : List A} → xs ↭ ys → List→FMSet xs ≡ List→FMSet ys
perm→FMSetPath' (↭-trans p q) = perm→FMSetPath' p ∙ perm→FMSetPath' q
perm→FMSetPath' {xs = []} {ys = []} ↭-[] = refl
perm→FMSetPath' {xs = x ∷ xs} {ys = y ∷ ys} (p ↭-∷ q) =
  cong₂ _∷_ p (perm→FMSetPath' q)
perm→FMSetPath' {xs = x ∷ x' ∷ xs} {ys = y ∷ y' ∷ ys} (↭-comm p q r) =
  comm x x' (List→FMSet xs)
    ∙ cong₃ (λ z w zs → z ∷ w ∷ zs) q p (perm→FMSetPath' r)

perm→FMSetPath : {xs ys : List A} → xs ∣↭∣ ys → List→FMSet xs ≡ List→FMSet ys
perm→FMSetPath = PT.rec (trunc _ _) perm→FMSetPath'

List↭→FMSet : List↭ A → FMSet A
List↭→FMSet = SQ.rec trunc List→FMSet (λ _ _ → perm→FMSetPath)

section' : (xs : List A) → FMSet→List↭ (List→FMSet xs) ≡ [ xs ]
section' [] = refl
section' (x ∷ xs) = cong (x ∷↭_) (section' xs)

section : (xs : List↭ A) → FMSet→List↭ (List↭→FMSet xs) ≡ xs
section = SQ.elimProp (λ _ → squash/ _ _) section'

List↭→FMSet-cons : (x : A) (xs : List↭ A) →
  List↭→FMSet (x ∷↭ xs) ≡ x ∷ List↭→FMSet xs
List↭→FMSet-cons x = SQ.elimProp (λ _ → trunc _ _) (λ _ → refl)

retract : (xs : FMSet A) → List↭→FMSet (FMSet→List↭ xs) ≡ xs
retract =
  FMSet.ElimProp.f (trunc _ _) refl λ x {xs} ih →
    List↭→FMSet-cons x (FMSet→List↭ xs) ∙ cong (x ∷_) ih

FMSetIsoList↭ : (A : Type ℓ) → Iso (FMSet A) (List↭ A)
FMSetIsoList↭ _ = iso FMSet→List↭ List↭→FMSet section retract

FMSet≡List↭ : (A : Type ℓ) → FMSet A ≡ List↭ A
FMSet≡List↭ A = isoToPath (FMSetIsoList↭ A)

-- Time to reap the rewards!

module _ {A : Type ℓ} where

  consPath : PathP (λ i → A → FMSet≡List↭ A i → FMSet≡List↭ A i) _∷_ _∷↭_
  consPath = funExt λ x → toPathP (funExt λ xs →
      transport (λ i → FMSet≡List↭ A i → FMSet≡List↭ A i) (x ∷_) xs
    ≡⟨⟩
      transport (FMSet≡List↭ A) (x ∷ transport (sym (FMSet≡List↭ A)) xs)
    ≡⟨ transportIsoToPath (FMSetIsoList↭ A) (x ∷ transport (sym (FMSet≡List↭ A)) xs) ⟩
      FMSet→List↭ (x ∷ transport (sym (FMSet≡List↭ A)) xs)
    ≡⟨ cong (FMSet→List↭ ∘ (x ∷_)) (transportIsoToPath⁻ (FMSetIsoList↭ A) xs) ⟩
      FMSet→List↭ (x ∷ List↭→FMSet xs)
    ≡⟨⟩
      x ∷↭ FMSet→List↭ (List↭→FMSet xs)
    ≡⟨ cong (x ∷↭_) (section xs) ⟩
      x ∷↭ xs
    ∎)

  drop-∷ : (x : A) (xs ys : FMSet A) → x ∷ xs ≡ x ∷ ys → xs ≡ ys
  drop-∷ =
    transport
      (λ i →
        (x : A) (xs ys : FMSet≡List↭ A (~ i)) →
        consPath (~ i) x xs ≡ consPath (~ i) x ys →
        xs ≡ ys)
      drop-∷↭

  differentHead : (x y : A) (xs ys : FMSet A) →
    ¬ x ≡ y →
    x ∷ xs ≡ y ∷ ys →
    ∃[ zs ∈ _ ] (xs ≡ y ∷ zs) × (x ∷ zs ≡ ys)
  differentHead =
    transport
      (λ i →
        (x y : A) (xs ys : FMSet≡List↭ A (~ i)) →
        ¬ x ≡ y →
        consPath (~ i) x xs ≡ consPath (~ i) y ys →
        ∃[ zs ∈ _ ] (xs ≡ consPath (~ i) y zs) × (consPath (~ i) x zs ≡ ys))
      differentHead↭

--------------------------------------------------------------------------------

module DiscreteFMSet {A : Type ℓ} where
  open PTMonad

  nilCase : (xs : FMSet A) → Dec ([] ≡ xs)
  nilCase =
    FMSet.ElimProp.f (isPropDec (trunc _ _))
      (yes refl) (λ _ _ → no (¬cons≡nil ∘ sym))

  find : (x : A) (x≟ : ∀ y → Dec (x ≡ y)) (xs : FMSet A) →
    Dec (∃[ ys ∈ _ ] x ∷ ys ≡ xs)
  find x x≟ =
    FMSet.ElimProp.f (isPropDec squash₁)
      (no (PT.rec isProp⊥ (¬cons≡nil ∘ snd)))
      (λ y {xs} ih →
        decRec
          (λ x≡y → yes ∣ xs , cong (_∷ xs) x≡y ∣₁)
          (λ x≢y →
            mapDec
              (λ ∃x∷ys≡xs → do
                (ys , x∷ys≡xs) ← ∃x∷ys≡xs
                return (y ∷ ys , comm x y ys ∙ cong (y ∷_) x∷ys≡xs))
              (λ ∄x∷ys≡xs ∃x∷ys≡y∷xs → ∄x∷ys≡xs do
                ys , x∷ys≡y∷xs ← ∃x∷ys≡y∷xs
                zs , _ , x∷zs≡xs ← differentHead x y ys xs x≢y x∷ys≡y∷xs
                return (zs , x∷zs≡xs))
              ih)
          (x≟ y))

  consCase : (x : A) (xs : FMSet A) →
    (x≟ : ∀ y → Dec (x ≡ y)) (xs≟ : ∀ ys → Dec (xs ≡ ys)) →
    (∀ ys → Dec (x ∷ xs ≡ ys))
  consCase x xs x≟ xs≟ ys =
    decRec
      (PT.rec (isPropDec (trunc _ _)) λ (zs , x∷zs≡ys) →
        mapDec
          (λ xs≡zs → cong (x ∷_) xs≡zs ∙ x∷zs≡ys)
          (λ xs≢zs x∷xs≡ys → xs≢zs (drop-∷ x xs zs (x∷xs≡ys ∙ sym x∷zs≡ys)))
          (xs≟ zs))
      (λ ∄x∷zs≡ys → no λ x∷xs≡ys → ∄x∷zs≡ys ∣ xs , x∷xs≡ys ∣₁)
      (find x x≟ ys)

  discreteFMSet : Discrete A → Discrete (FMSet A)
  discreteFMSet discreteA =
    FMSet.ElimProp.f (isPropΠ λ _ → isPropDec (trunc _ _))
      nilCase (λ x {xs} → consCase x xs (discreteA x))


open DiscreteFMSet using (discreteFMSet) public

module Test where private
  open import Cubical.Data.Nat using (discreteℕ)

  _≟_ = discreteFMSet discreteℕ

  _ : (1 ∷ 2 ∷ 3 ∷ []) ≟ (3 ∷ 2 ∷ 1 ∷ [])
    ≡ yes
        (congS (1 ∷_)
            ((congS (2 ∷_) (refl ∙ refl)
              ∙ comm 2 3 []
              ∙ refl))
          ∙ comm 1 3 (2 ∷ [])
          ∙ congS (3 ∷_) (comm 1 2 [] ∙ refl))
  _ = refl

  _ : (1 ∷ 2 ∷ 3 ∷ 2 ∷ 1 ∷ []) ≟ (3 ∷ 1 ∷ 1 ∷ 2 ∷ 2 ∷ []) ≡ yes _
  _ = refl

  _ : (1 ∷ 2 ∷ 3 ∷ 2 ∷ 1 ∷ []) ≟ (3 ∷ 1 ∷ 1 ∷ 2 ∷ 10 ∷ []) ≡ no _
  _ = refl
