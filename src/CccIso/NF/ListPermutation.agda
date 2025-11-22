module CccIso.NF.ListPermutation where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function using (_∘_)
open import Cubical.Foundations.HLevels using (isProp→)
open import Cubical.Foundations.Isomorphism using
  (Iso; iso; isoToEquiv; isoToPath; transportIsoToPath; transportIsoToPath⁻)
open import Cubical.Foundations.Univalence using (ua; uaβ; ~uaβ)
open import Cubical.Data.Empty using (⊥*)
open import Cubical.Data.List as List using (List; []; _∷_; _++_; module ListPath)
open import Cubical.Data.Nat.Base using (ℕ)
open import Cubical.Data.Sigma using (Σ-syntax; _×_; _,_)
open import Cubical.Data.Sum using (_⊎_; inl; inr)
open import Cubical.Data.Unit using (Unit*; tt*)
open import Cubical.HITs.FiniteMultiset as FMSet using (FMSet; []; _∷_; comm; trunc)
open import Cubical.HITs.PropositionalTruncation as PT using (∥_∥₁; ∣_∣₁; squash₁)
open import Cubical.HITs.SetTruncation as ST using (∥_∥₂; ∣_∣₂; squash₂)
open import Cubical.HITs.SetQuotients as SQ using (_/_; [_]; eq/; squash/)
open import Cubical.HITs.Truncation using (∥_∥_; ∣_∣; ∣_∣ₕ; PathIdTrunc; propTrunc≡Trunc1; propTrunc≡Trunc2)
open import Cubical.Relation.Binary using (module BinaryRelation)

open import CccIso.NF

open BinaryRelation
open Iso

private
  variable
    ℓ : Level
    A : Type ℓ
    n : ℕ

infix  4 _∣↭∣_
infixr 5 _∷↭_ _∣*ᶠ∣_

--------------------------------------------------------------------------------
-- Permutation relation
-- Ref: https://github.com/agda/agda-stdlib/blob/master/src/Data/List/Relation/Binary/Permutation/Setoid/Properties.agda

module _ {A : Type ℓ} where
  infix  4 _↭_ _↭′_ _↭″_
  infixr 5 _↭-∷_

  data _↭_ (xs ys : List A) : Type ℓ
  _↭′_ _↭″_ : List A → List A → Type ℓ
  Swap : A → A → List A → List A → Type ℓ

  data _↭_ xs ys where
    con : xs ↭′ ys → xs ↭ ys

  xs ↭′ ys = (xs ↭″ ys) ⊎ (Σ[ zs ∈ _ ] (xs ↭ zs) × (zs ↭ ys))

  [] ↭″ [] = Unit*
  [] ↭″ y ∷ ys = ⊥*
  x ∷ xs ↭″ [] = ⊥*
  x ∷ xs ↭″ y ∷ ys = ((x ≡ y) × (xs ↭ ys)) ⊎ Swap x y xs ys

  Swap x y [] _ = ⊥*
  Swap x y (x' ∷ xs) [] = ⊥*
  Swap x y (x' ∷ xs) (y' ∷ ys) = (x ≡ y') × (x' ≡ y) × (xs ↭ ys)

  pattern ↭-[] = con (inl tt*)
  pattern _↭-∷_ p q = con (inl (inl (p , q)))
  pattern ↭-trans {zs} p q = con (inr (zs , p , q))
  pattern ↭-swap p q r = con (inl (inr (p , q , r)))

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
  _ = ↭-swap

  ↭-refl : ∀ {xs} → xs ↭ xs
  ↭-refl {xs = []} = ↭-[]
  ↭-refl {xs = x ∷ xs} = refl ↭-∷ ↭-refl

  ↭-sym : ∀ {xs ys} → xs ↭ ys → ys ↭ xs
  ↭-sym (↭-trans p q) = ↭-trans (↭-sym q) (↭-sym p)
  ↭-sym {xs = []} {ys = []} ↭-[] = ↭-[]
  ↭-sym {xs = x ∷ xs} {ys = y ∷ ys} (p ↭-∷ q) = sym p ↭-∷ ↭-sym q
  ↭-sym {xs = x ∷ x' ∷ xs} {ys = y ∷ y' ∷ ys} (↭-swap p q r) =
    ↭-swap (sym q) (sym p) (↭-sym r)

  shift : ∀ {x y} → x ≡ y → ∀ xs ys → x ∷ xs ++ ys ↭ xs ++ y ∷ ys
  shift p [] ys = p ↭-∷ ↭-refl
  shift p (x ∷ xs) ys =
    ↭-trans (↭-swap refl refl ↭-refl) (refl ↭-∷ shift p xs ys)

  split-helper : ∀ {x} xs ys as bs →
    xs ↭ ys →
    ListPath.Cover ys (as ++ x ∷ bs) →
    Σ[ ps ∈ _ ] Σ[ qs ∈ _ ]
      ListPath.Cover xs (ps ++ x ∷ qs) × (ps ++ qs ↭ as ++ bs)
  split-helper xs ys as bs (↭-trans p q) eq
    using ps , qs , eq' , r ← split-helper _ ys as bs q eq
    using ps' , qs' , eq'' , s ← split-helper xs _ ps qs p eq'
    = ps' , qs' , eq'' , ↭-trans s r
  split-helper [] [] [] bs ↭-[] ()
  split-helper [] [] (_ ∷ _) bs ↭-[] ()
  split-helper (x ∷ xs) (y ∷ ys) [] bs (p ↭-∷ q) (eq , eq') =
    [] , xs ,
    (p ∙ eq , ListPath.reflCode xs) ,
    ↭-trans q (subst (ys ↭_) (ListPath.decode ys bs eq') ↭-refl)
  split-helper (x ∷ xs) (y ∷ ys) (a ∷ as) bs (p ↭-∷ q) (eq , eq')
    using ps , qs , eq' , r ← split-helper xs ys as bs q eq'
    = a ∷ ps , qs , (p ∙ eq , eq') , refl ↭-∷ r
  split-helper (x ∷ y ∷ xs) (x' ∷ y' ∷ xs') [] (b ∷ _) (↭-swap p q r) (eq , eq' , eq'') =
    b ∷ [] , xs ,
    (p ∙ eq' , q ∙ eq , ListPath.reflCode xs) ,
    refl ↭-∷ ↭-trans r (subst (xs' ↭_) (ListPath.decode xs' _ eq'') ↭-refl)
  split-helper (x ∷ y ∷ xs) (x' ∷ y' ∷ xs') (a ∷ []) bs (↭-swap p q r) (eq , eq' , eq'') =
    [] , a ∷ xs ,
    (p ∙ eq' , q ∙ eq , ListPath.reflCode xs) ,
    refl ↭-∷ ↭-trans r (subst (xs' ↭_) (ListPath.decode xs' _ eq'') ↭-refl)
  split-helper (x ∷ y ∷ xs) (x' ∷ y' ∷ xs') (a ∷ b ∷ as) bs (↭-swap p q r) (eq , eq' , eq'')
    using ps , qs , eq''' , s ← split-helper xs xs' as bs r eq''
    = b ∷ a ∷ ps , qs ,
      (p ∙ eq' , q ∙ eq , eq''') ,
      ↭-swap refl refl s

  split : ∀ {x xs ys zs} → xs ↭ (ys ++ x ∷ zs) →
    Σ[ ps ∈ _ ] Σ[ qs ∈ _ ]
      ListPath.Cover xs (ps ++ x ∷ qs) × (ps ++ qs ↭ ys ++ zs)
  split {x = x} {xs = xs} {ys = ys} {zs = zs} p =
    split-helper xs (ys ++ x ∷ zs) ys zs p (ListPath.reflCode _)

  ↭-dropMiddleElement-Cover : ∀ {x} ws xs {ys zs} →
    ListPath.Cover (ws ++ x ∷ ys) (xs ++ x ∷ zs) →
    ws ++ ys ↭ xs ++ zs
  ↭-dropMiddleElement-Cover [] [] (_ , eq) =
    subst (_ ↭_) (ListPath.decode _ _ eq) ↭-refl
  ↭-dropMiddleElement-Cover [] (x ∷ xs) (eq , eq') =
    ↭-trans
      (subst (_ ↭_) (ListPath.decode _ _ eq') ↭-refl)
      (↭-sym (shift (sym eq) xs _))
  ↭-dropMiddleElement-Cover (w ∷ ws) [] (eq , eq') =
    ↭-trans
      (shift eq ws _)
      (subst (_ ↭_) (ListPath.decode _ _ eq') ↭-refl)
  ↭-dropMiddleElement-Cover (w ∷ ws) (x ∷ xs) (eq , eq') =
    eq ↭-∷ ↭-dropMiddleElement-Cover ws xs eq'

  ↭-dropMiddleElement : ∀ {x} ws xs {ys zs} →
    ws ++ x ∷ ys ↭ xs ++ x ∷ zs →
    ws ++ ys ↭ xs ++ zs
  ↭-dropMiddleElement ws xs p
    using ps , qs , eq , q ← split p
    = ↭-trans (↭-dropMiddleElement-Cover ws ps eq) q

  ↭-drop-∷ : ∀ {x xs ys} → x ∷ xs ↭ x ∷ ys → xs ↭ ys
  ↭-drop-∷ = ↭-dropMiddleElement [] []

--------------------------------------------------------------------------------
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

swap↭ : (x y : A) (xs : List↭ A) → x ∷↭ y ∷↭ xs ≡ y ∷↭ x ∷↭ xs
swap↭ x y =
  SQ.elimProp
    (λ _ → squash/ _ _)
    (λ _ → eq/ _ _ ∣ ↭-swap refl refl ↭-refl ∣₁)

reify↭ : {xs ys : List A} → [ xs ] ≡ [ ys ] → xs ∣↭∣ ys
reify↭ = SQ.effective (λ _ _ → squash₁) isEquivRel∣↭∣ _ _

drop-∷↭ : (x : A) (xs ys : List↭ A) → x ∷↭ xs ≡ x ∷↭ ys → xs ≡ ys
drop-∷↭ x =
  SQ.elimProp2
    (λ _ _ → isProp→ (squash/ _ _))
    (λ _ _ → PT.rec (squash/ _ _) (eq/ _ _ ∘ ∣_∣₁ ∘ ↭-drop-∷) ∘ reify↭)

--------------------------------------------------------------------------------
-- ∥ NF n ∥₂ ≃ List↭ (Factor n)

NF→List↭ : NF n → List↭ (Factor n)
NF→List↭ = recSetNF squash/ []↭ _∷↭_ swap↭

∥NF∥₂→List↭ : ∥ NF n ∥₂ → List↭ (Factor n)
∥NF∥₂→List↭ = ST.rec squash/ NF→List↭

pattern ∣⊤∣ = ∣ ⊤ ∣₂

_∣*ᶠ∣_ : Factor n → ∥ NF n ∥₂ → ∥ NF n ∥₂
_∣*ᶠ∣_ φ = ST.map (φ *ᶠ_)

∣swap∣ : (φ ψ : Factor n) (α : ∥ NF n ∥₂) →
  φ ∣*ᶠ∣ ψ ∣*ᶠ∣ α ≡ ψ ∣*ᶠ∣ φ ∣*ᶠ∣ α
∣swap∣ φ ψ =
  ST.elim (λ _ → isProp→isSet (squash₂ _ _)) (cong ∣_∣₂ ∘ swap φ ψ)

List→∥NF∥₂ : List (Factor n) → ∥ NF n ∥₂
List→∥NF∥₂ = List.foldr _∣*ᶠ∣_ ∣⊤∣

List→∥NF∥₂-Path' : (xs ys : List (Factor n))
  → xs ↭ ys
  → List→∥NF∥₂ xs ≡ List→∥NF∥₂ ys
List→∥NF∥₂-Path' xs ys (↭-trans p q) =
  List→∥NF∥₂-Path' xs _ p ∙ List→∥NF∥₂-Path' _ ys q
List→∥NF∥₂-Path' [] [] ↭-[] = refl
List→∥NF∥₂-Path' (φ ∷ α) (ψ ∷ β) (p ↭-∷ q) =
  cong₂ _∣*ᶠ∣_ p (List→∥NF∥₂-Path' α β q)
List→∥NF∥₂-Path' (φ ∷ φ' ∷ α) (ψ ∷ ψ' ∷ β) (↭-swap p q r) =
  ∣swap∣ φ φ' (List→∥NF∥₂ α)
    ∙ cong₃ (λ θ θ' γ → θ ∣*ᶠ∣ θ' ∣*ᶠ∣ γ) q p (List→∥NF∥₂-Path' α β r)

List→∥NF∥₂-Path : (α β : List (Factor n))
  → α ∣↭∣ β
  → List→∥NF∥₂ α ≡ List→∥NF∥₂ β
List→∥NF∥₂-Path α β = PT.rec (squash₂ _ _) (List→∥NF∥₂-Path' α β)

List↭→∥NF∥₂ : List↭ (Factor n) → ∥ NF n ∥₂
List↭→∥NF∥₂ = SQ.rec squash₂ List→∥NF∥₂ List→∥NF∥₂-Path

∥NF∥₂→List↭-cons : (φ : Factor n) (α : ∥ NF n ∥₂) →
  ∥NF∥₂→List↭ (φ ∣*ᶠ∣ α) ≡ φ ∷↭ ∥NF∥₂→List↭ α
∥NF∥₂→List↭-cons φ =
  ST.elim (λ _ → isProp→isSet (squash/ _ _)) (λ _ → refl)

section' : (α : List (Factor n)) → ∥NF∥₂→List↭ (List→∥NF∥₂ α) ≡ [ α ]
section' [] = refl
section' (φ ∷ α) =
  ∥NF∥₂→List↭-cons φ (List→∥NF∥₂ α) ∙ cong (φ ∷↭_) (section' α)

section : (α : List↭ (Factor n)) → ∥NF∥₂→List↭ (List↭→∥NF∥₂ α) ≡ α
section = SQ.elimProp (λ _ → squash/ _ _) section'

List↭→∥NF∥₂-cons : (φ : Factor n) (α : List↭ (Factor n)) →
  List↭→∥NF∥₂ (φ ∷↭ α) ≡ φ ∣*ᶠ∣ List↭→∥NF∥₂ α
List↭→∥NF∥₂-cons φ = SQ.elimProp (λ _ → squash₂ _ _) (λ _ → refl)

retract' : (α : NF n) → List↭→∥NF∥₂ (NF→List↭ α) ≡ ∣ α ∣₂
retract' =
  elimPropNF
    (λ _ → squash₂ _ _)
    refl
    (λ φ {α} ih → List↭→∥NF∥₂-cons φ (NF→List↭ α) ∙ cong (φ ∣*ᶠ∣_) ih)

retract : (α : ∥ NF n ∥₂) → List↭→∥NF∥₂ (∥NF∥₂→List↭ α) ≡ α
retract = ST.elim (λ _ → isProp→isSet (squash₂ _ _)) retract'

∥NF∥₂IsoList↭ : Iso ∥ NF n ∥₂ (List↭ (Factor n))
∥NF∥₂IsoList↭ = iso ∥NF∥₂→List↭ List↭→∥NF∥₂ section retract

∥NF∥₂≡List↭ : ∥ NF n ∥₂ ≡ List↭ (Factor n)
∥NF∥₂≡List↭ = isoToPath ∥NF∥₂IsoList↭

--------------------------------------------------------------------------------
-- Transport lemmas along the isomorphism

consPath :
  PathP
    (λ i → Factor n → ∥NF∥₂≡List↭ {n} i → ∥NF∥₂≡List↭ {n} i)
    _∣*ᶠ∣_
    _∷↭_
consPath {n} = funExt λ φ → toPathP (funExt λ α →
    transport (λ i → ∥NF∥₂≡List↭ {n} i → ∥NF∥₂≡List↭ {n} i) (φ ∣*ᶠ∣_) α
  ≡⟨⟩
    transport (∥NF∥₂≡List↭ {n})
      (φ ∣*ᶠ∣ transport (sym (∥NF∥₂≡List↭ {n})) α)
  ≡⟨ transportIsoToPath
      (∥NF∥₂IsoList↭ {n})
      (φ ∣*ᶠ∣ transport (sym (∥NF∥₂≡List↭ {n})) α)
  ⟩
    ∥NF∥₂→List↭
      (φ ∣*ᶠ∣ transport (sym (∥NF∥₂≡List↭ {n})) α)
  ≡⟨ cong
      (∥NF∥₂→List↭ ∘ (φ ∣*ᶠ∣_))
      (transportIsoToPath⁻ (∥NF∥₂IsoList↭ {n}) α)
  ⟩
    ∥NF∥₂→List↭ (φ ∣*ᶠ∣ List↭→∥NF∥₂ α)
  ≡⟨ ∥NF∥₂→List↭-cons φ (List↭→∥NF∥₂ α) ⟩
    φ ∷↭ ∥NF∥₂→List↭ (List↭→∥NF∥₂ α)
  ≡⟨ cong (φ ∷↭_) (section α) ⟩
    φ ∷↭ α
  ∎)

drop-∷' : (φ : Factor n) (α β : ∥ NF n ∥₂) → φ ∣*ᶠ∣ α ≡ φ ∣*ᶠ∣ β → α ≡ β
drop-∷' {n = n} =
  transport
    (λ i →
      (φ : Factor n) (α β : ∥NF∥₂≡List↭ {n} (~ i)) →
      consPath (~ i) φ α ≡ consPath (~ i) φ β →
      α ≡ β)
    drop-∷↭

PathIdTrunc1 : (x y : A) → (∣ x ∣₂ ≡ ∣ y ∣₂) ≡ ∥ x ≡ y ∥₁
PathIdTrunc1 {ℓ} {A} x y =
    ∣ x ∣₂ ≡ ∣ y ∣₂
  ≡⟨ cong₃
      Path
      propTrunc≡Trunc2
      (toPathP (cong ∣_∣ (transportRefl x)))
      (toPathP (cong ∣_∣ (transportRefl y)))
  ⟩
    ∣ x ∣ₕ ≡ ∣ y ∣ₕ
  ≡⟨ PathIdTrunc 1 ⟩
    (∥ x ≡ y ∥ 1)
  ≡⟨ sym propTrunc≡Trunc1 ⟩
    ∥ x ≡ y ∥₁
  ∎

drop-∷ : (φ : Factor n) (α β : NF n) → ∥ φ *ᶠ α ≡ φ *ᶠ β ∥₁ → ∥ α ≡ β ∥₁
drop-∷ φ α β =
  transport
    (λ i → PathIdTrunc1 (φ *ᶠ α) (φ *ᶠ β) i → PathIdTrunc1 α β i)
    (drop-∷' φ ∣ α ∣₂ ∣ β ∣₂)
