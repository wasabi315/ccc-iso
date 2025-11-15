module CccIso.NF where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels using
  (isGroupoid→CubeP; isSet→SquareP; isSet→isGroupoid)
open import Cubical.Data.Fin.Recursive.Base using (Fin)
open import Cubical.Data.Nat.Base using (ℕ)

infixr 5 _⇒ι_ _⇒ᶠ_ _⇒_
infixr 6 _*ᶠ_ _*_

private
  variable
    n : ℕ

--------------------------------------------------------------------------------

data Factor (n : ℕ) : Type
data NF (n : ℕ) : Type

data Factor n where
  _⇒ι_ : (α : NF n) (x : Fin n) → Factor n

-- Bag of factors
data NF n where
  ⊤    : NF n
  _*ᶠ_ : (φ : Factor n) (α : NF n) → NF n

  swap : ∀ φ ψ α → φ *ᶠ ψ *ᶠ α ≡ ψ *ᶠ φ *ᶠ α

  -- swap is involutive
  invol : ∀ φ ψ α → swap φ ψ α ≡ sym (swap ψ φ α)

  -- identify the two different paths from ε * φ * ψ * ν to ψ * φ * ε * ν
  hexagon : ∀ ε φ ψ α →
    Path (ε *ᶠ φ *ᶠ ψ *ᶠ α ≡ ψ *ᶠ φ *ᶠ ε *ᶠ α)
      (swap ε φ (ψ *ᶠ α)
        ∙∙ cong (φ *ᶠ_) (swap ε ψ α)
        ∙∙ swap φ ψ (ε *ᶠ α))
      (cong (ε *ᶠ_) (swap φ ψ α)
        ∙∙ swap ε ψ (φ *ᶠ α)
        ∙∙ cong (ψ *ᶠ_) (swap ε φ α))

  -- only groupoid truncate to allow interpretation into hSet
  trunc : ∀ α β (p q : α ≡ β) (P Q : p ≡ q) → P ≡ Q

--------------------------------------------------------------------------------
-- Eliminators for NF

doubleCompPathP : ∀ {a b} {A : Type a} {B : A → Type b} →
  {x y z w : A} {x' : B x} {y' : B y} {z' : B z} {w' : B w} →
  {p : x ≡ y} {q : y ≡ z} {r : z ≡ w} →
  PathP (λ i → B (p i)) x' y' →
  PathP (λ i → B (q i)) y' z' →
  PathP (λ i → B (r i)) z' w' →
  PathP (λ i → B ((p ∙∙ q ∙∙ r) i)) x' w'
doubleCompPathP {B = B} {p = p} {q = q} {r = r} P Q R i =
  comp
    (λ j → B (doubleCompPath-filler p q r j i))
    (λ where
      j (i = i0) → P (~ j)
      j (i = i1) → R j)
    (Q i)

doubleCompPathP-filler : ∀ {a b} {A : Type a} {B : A → Type b} →
  {x y z w : A} {x' : B x} {y' : B y} {z' : B z} {w' : B w} →
  {p : x ≡ y} {q : y ≡ z} {r : z ≡ w} →
  (P : PathP (λ i → B (p i)) x' y') →
  (Q : PathP (λ i → B (q i)) y' z') →
  (R : PathP (λ i → B (r i)) z' w') →
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
doubleCompPathP≡doubleCompPath : ∀ {a} {A : Type a} {x y z w : A} →
  (p : x ≡ y) (q : y ≡ z) (r : z ≡ w) →
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

module _ {n ℓ} {B : Type ℓ} (trunc* : isGroupoid B)
  (⊤* : B)
  (_**_ : Factor n → B → B)
  (swap* : ∀ φ ψ α* → φ ** (ψ ** α*) ≡ ψ ** (φ ** α*))
  (invol* : ∀ φ ψ α* → swap* φ ψ α* ≡ sym (swap* ψ φ α*))
  (hexagon* : ∀ ε φ ψ α* →
    Path (ε ** (φ ** (ψ ** α*)) ≡ ψ ** (φ ** (ε ** α*)))
      (swap* ε φ (ψ ** α*)
        ∙∙ cong (φ **_) (swap* ε ψ α*)
        ∙∙ swap* φ ψ (ε ** α*))
      (cong (ε **_) (swap* φ ψ α*)
        ∙∙ swap* ε ψ (φ ** α*)
        ∙∙ cong (ψ **_) (swap* ε φ α*)))
  where

  recNF : NF n → B
  recNF ⊤ = ⊤*
  recNF (φ *ᶠ α) = φ ** recNF α
  recNF (swap φ ψ α i) = swap* φ ψ (recNF α) i
  recNF (invol φ ψ α i j) = invol* φ ψ (recNF α) i j
  recNF (hexagon ε φ ψ α i j) =
    (doubleCompPathP≡doubleCompPath _ _ _
      ∙∙ hexagon* ε φ ψ (recNF α)
      ∙∙ sym (doubleCompPathP≡doubleCompPath _ _ _))
    i j
  recNF (trunc α β p q P Q i j k) =
    trunc*
      (recNF α) (recNF β)
      (λ i → recNF (p i)) (λ i → recNF (q i))
      (λ i j → recNF (P i j)) (λ i j → recNF (Q i j))
      i j k


module _ {n ℓ} {B : NF n → Type ℓ} (trunc* : ∀ α → isSet (B α))
  (⊤* : B ⊤)
  (_**_ : ∀ φ {α} (α* : B α) → B (φ *ᶠ α))
  (swap* : ∀ φ ψ {α} (α* : B α) →
    PathP (λ i → B (swap φ ψ α i)) (φ ** (ψ ** α*)) (ψ ** (φ ** α*)))
  where

  elimSetNF : ∀ α → B α
  elimSetNF ⊤ = ⊤*
  elimSetNF (φ *ᶠ α) = φ ** elimSetNF α
  elimSetNF (swap φ ψ α i) = swap* φ ψ (elimSetNF α) i
  elimSetNF (invol φ ψ α i j) =
    isSet→SquareP (λ i j → trunc* (invol φ ψ α i j))
      (swap* φ ψ (elimSetNF α))
      (symP (swap* ψ φ (elimSetNF α)))
      refl
      refl
      i j
  elimSetNF (hexagon ε φ ψ α i j) =
    isSet→SquareP (λ i j → trunc* (hexagon ε φ ψ α i j))
      (doubleCompPathP {B = B}
        (swap* ε φ (ψ ** elimSetNF α))
        (congP (λ _ → φ **_) (swap* ε ψ (elimSetNF α)))
        (swap* φ ψ (ε ** elimSetNF α)))
      (doubleCompPathP {B = B}
        (congP (λ _ → ε **_) (swap* φ ψ (elimSetNF α)))
        (swap* ε ψ (φ ** elimSetNF α))
        (congP (λ _ → ψ **_) (swap* ε φ (elimSetNF α))))
      refl
      refl
      i j
  elimSetNF (trunc α β p q P Q i j k) =
    isGroupoid→CubeP
      (λ i j k → B (trunc α β p q P Q i j k))
      (λ j k → elimSetNF (P j k))
      (λ j k → elimSetNF (Q j k))
      (λ i k → elimSetNF (p k))
      (λ i k → elimSetNF (q k))
      (λ i j → elimSetNF α)
      (λ i j → elimSetNF β)
      (isSet→isGroupoid (trunc* _))
      i j k


module _ {n ℓ} {B : NF n → Type ℓ} (trunc* : ∀ α → isProp (B α))
  (⊤* : B ⊤)
  (_**_ : ∀ φ {α} (α* : B α) → B (φ *ᶠ α))
  where

  elimPropNF : ∀ α → B α
  elimPropNF =
    elimSetNF
      (λ α → isProp→isSet (trunc* α))
      ⊤*
      _**_
      (λ φ ψ {α} α* →
        isProp→PathP
          (λ i → trunc* (swap φ ψ α i))
          (φ ** (ψ ** α*))
          (ψ ** (φ ** α*)))

--------------------------------------------------------------------------------
-- Product and exponential for NF

_*_ : NF n → NF n → NF n
α * β = recNF trunc β _*ᶠ_ swap invol hexagon α

-- uncurry
_⇒ᶠ_ : NF n → Factor n → Factor n
α ⇒ᶠ (β ⇒ι x) = (α * β) ⇒ι x

-- distribute exponential over products
_⇒_ : NF n → NF n → NF n
_⇒_ α =
  recNF
    trunc
    ⊤
    (λ φ α⇒β → (α ⇒ᶠ φ) *ᶠ α⇒β)
    (λ φ ψ α⇒β → swap (α ⇒ᶠ φ) (α ⇒ᶠ ψ) α⇒β)
    (λ φ ψ α⇒β → invol (α ⇒ᶠ φ) (α ⇒ᶠ ψ) α⇒β)
    (λ ε φ ψ α⇒β → hexagon (α ⇒ᶠ ε) (α ⇒ᶠ φ) (α ⇒ᶠ ψ) α⇒β)

--------------------------------------------------------------------------------
-- Simultaneous interpretation of NF and Factor

record Model ℓ ℓ' : Type (ℓ-suc (ℓ-max ℓ ℓ')) where
  no-eta-equality
  infixr 5 _⇒ιᴹ_
  infixr 6 _*ᴹ_
  field
    Factorᴹ : ℕ → Type ℓ
    NFᴹ : ℕ → Type ℓ'

    _⇒ιᴹ_ : NFᴹ n → Fin n → Factorᴹ n

    ⊤ᴹ : NFᴹ n
    _*ᴹ_ : Factorᴹ n → NFᴹ n → NFᴹ n
    swapᴹ : (φ ψ : Factorᴹ n) (α : NFᴹ n) →
      φ *ᴹ ψ *ᴹ α ≡ ψ *ᴹ φ *ᴹ α
    involᴹ : (φ ψ : Factorᴹ n) (α : NFᴹ n) →
      swapᴹ φ ψ α ≡ sym (swapᴹ ψ φ α)
    hexagonᴹ : (ε φ ψ : Factorᴹ n) (α : NFᴹ n) →
      Path (ε *ᴹ φ *ᴹ ψ *ᴹ α ≡ ψ *ᴹ φ *ᴹ ε *ᴹ α)
        (swapᴹ ε φ (ψ *ᴹ α)
          ∙∙ cong (φ *ᴹ_) (swapᴹ ε ψ α)
          ∙∙ swapᴹ φ ψ (ε *ᴹ α))
        (cong (ε *ᴹ_) (swapᴹ φ ψ α)
          ∙∙ swapᴹ ε ψ (φ *ᴹ α)
          ∙∙ cong (ψ *ᴹ_) (swapᴹ ε φ α))
    truncNFᴹ : isGroupoid (NFᴹ n)

module Rec {ℓ ℓ'} (M : Model ℓ ℓ') where
  open Model M

  ⟦_⟧ᶠ : Factor n → Factorᴹ n
  ⟦_⟧ⁿ : NF n → NFᴹ n

  ⟦ α ⇒ι x ⟧ᶠ = ⟦ α ⟧ⁿ ⇒ιᴹ x

  ⟦ ⊤ ⟧ⁿ = ⊤ᴹ
  ⟦ φ *ᶠ α ⟧ⁿ = ⟦ φ ⟧ᶠ *ᴹ ⟦ α ⟧ⁿ
  ⟦ swap φ ψ α i ⟧ⁿ = swapᴹ ⟦ φ ⟧ᶠ ⟦ ψ ⟧ᶠ ⟦ α ⟧ⁿ i
  ⟦ invol φ ψ α i j ⟧ⁿ = involᴹ ⟦ φ ⟧ᶠ ⟦ ψ ⟧ᶠ ⟦ α ⟧ⁿ i j
  ⟦ hexagon ε φ ψ α i j ⟧ⁿ =
    (doubleCompPathP≡doubleCompPath _ _ _
      ∙∙ hexagonᴹ ⟦ ε ⟧ᶠ ⟦ φ ⟧ᶠ ⟦ ψ ⟧ᶠ ⟦ α ⟧ⁿ
      ∙∙ sym (doubleCompPathP≡doubleCompPath _ _ _))
    i j
  ⟦ trunc α β p q P Q i j k ⟧ⁿ =
    truncNFᴹ
      ⟦ α ⟧ⁿ ⟦ β ⟧ⁿ
      (λ i → ⟦ p i ⟧ⁿ) (λ i → ⟦ q i ⟧ⁿ)
      (λ i j → ⟦ P i j ⟧ⁿ) (λ i j → ⟦ Q i j ⟧ⁿ)
      i j k


record ModelDep ℓ ℓ' : Type (ℓ-suc (ℓ-max ℓ ℓ')) where
  no-eta-equality
  infixr 5 _⇒ιᴹ_
  infixr 6 _*ᴹ_
  field
    Factorᴹ : Factor n → Type ℓ
    NFᴹ : NF n → Type ℓ'

    _⇒ιᴹ_ : {α : NF n} → NFᴹ α → (x : Fin n) → Factorᴹ (α ⇒ι x)

    ⊤ᴹ : NFᴹ {n = n} ⊤
    _*ᴹ_ : {φ : Factor n} {α : NF n} → Factorᴹ φ → NFᴹ α → NFᴹ (φ *ᶠ α)
    swapᴹ : {φ ψ : Factor n} {α : NF n} →
      (φᴹ : Factorᴹ φ) (ψᴹ : Factorᴹ ψ) (αᴹ : NFᴹ α) →
      PathP (λ i → NFᴹ (swap φ ψ α i))
        (φᴹ *ᴹ ψᴹ *ᴹ αᴹ)
        (ψᴹ *ᴹ φᴹ *ᴹ αᴹ)
    involᴹ : {φ ψ : Factor n} {α : NF n} →
      (φᴹ : Factorᴹ φ) (ψᴹ : Factorᴹ ψ) (αᴹ : NFᴹ α) →
      SquareP (λ i j → NFᴹ (invol φ ψ α i j))
        (swapᴹ φᴹ ψᴹ αᴹ)
        (symP (swapᴹ ψᴹ φᴹ αᴹ))
        refl
        refl
    hexagonᴹ : {ε φ ψ : Factor n} {α : NF n} →
      (εᴹ : Factorᴹ ε) (φᴹ : Factorᴹ φ) (ψᴹ : Factorᴹ ψ) (αᴹ : NFᴹ α) →
      SquareP (λ i j → NFᴹ (hexagon ε φ ψ α i j))
        (doubleCompPathP {B = NFᴹ}
          (swapᴹ εᴹ φᴹ (ψᴹ *ᴹ αᴹ))
          (congP (λ _ → φᴹ *ᴹ_) (swapᴹ εᴹ ψᴹ αᴹ))
          (swapᴹ φᴹ ψᴹ (εᴹ *ᴹ αᴹ)))
        (doubleCompPathP {B = NFᴹ}
          (congP (λ _ → εᴹ *ᴹ_) (swapᴹ φᴹ ψᴹ αᴹ))
          (swapᴹ εᴹ ψᴹ (φᴹ *ᴹ αᴹ))
          (congP (λ _ → ψᴹ *ᴹ_) (swapᴹ εᴹ φᴹ αᴹ)))
        refl
        refl
    truncNFᴹ : (α : NF n) → isGroupoid (NFᴹ α)

module Elim {ℓ ℓ'} (M : ModelDep ℓ ℓ') where
  open ModelDep M

  ⟦_⟧ᶠ : (α : Factor n) → Factorᴹ α
  ⟦_⟧ⁿ : (α : NF n) → NFᴹ α

  ⟦ α ⇒ι x ⟧ᶠ = ⟦ α ⟧ⁿ ⇒ιᴹ x
  ⟦ ⊤ ⟧ⁿ = ⊤ᴹ
  ⟦ φ *ᶠ α ⟧ⁿ = ⟦ φ ⟧ᶠ *ᴹ ⟦ α ⟧ⁿ
  ⟦ swap φ ψ α i ⟧ⁿ = swapᴹ ⟦ φ ⟧ᶠ ⟦ ψ ⟧ᶠ ⟦ α ⟧ⁿ i
  ⟦ invol φ ψ α i j ⟧ⁿ = involᴹ ⟦ φ ⟧ᶠ ⟦ ψ ⟧ᶠ ⟦ α ⟧ⁿ i j
  ⟦ hexagon ε φ ψ α i j ⟧ⁿ = hexagonᴹ ⟦ ε ⟧ᶠ ⟦ φ ⟧ᶠ ⟦ ψ ⟧ᶠ ⟦ α ⟧ⁿ i j
  ⟦ trunc α β p q P Q i j k ⟧ⁿ =
    isGroupoid→CubeP
      (λ i j k → NFᴹ (trunc α β p q P Q i j k))
      (λ j k → ⟦ P j k ⟧ⁿ)
      (λ j k → ⟦ Q j k ⟧ⁿ)
      (λ i k → ⟦ p k ⟧ⁿ)
      (λ i k → ⟦ q k ⟧ⁿ)
      (λ i j → ⟦ α ⟧ⁿ)
      (λ i j → ⟦ β ⟧ⁿ)
      (truncNFᴹ _)
      i j k
