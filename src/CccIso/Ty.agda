module CccIso.Ty where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Data.Fin.Recursive.Base using (Fin)
open import Cubical.Data.Nat.Base using (ℕ)

infixr 5 _⇒_
infixr 6 _*_

private
  variable
    n : ℕ

--------------------------------------------------------------------------------

data Ty (n : ℕ) : Type where
  ι   : (x : Fin n) → Ty n
  ⊤   : Ty n
  _*_ : (A B : Ty n) → Ty n
  _⇒_ : (A B : Ty n) → Ty n

  *-identityˡ : ∀ A → ⊤ * A ≡ A
  *-identityʳ : ∀ A → A * ⊤ ≡ A
  *-comm      : ∀ A B → A * B ≡ B * A
  *-assoc     : ∀ A B C → (A * B) * C ≡ A * (B * C)

  ⇒-identityˡ : ∀ A → A ≡ ⊤ ⇒ A
  ⇒-curry     : ∀ A B C → A ⇒ (B ⇒ C) ≡ (A * B) ⇒ C
  ⇒-annihilʳ  : ∀ A → A ⇒ ⊤ ≡ ⊤
  ⇒-distribˡ  : ∀ A B C → A ⇒ (B * C) ≡ (A ⇒ B) * (A ⇒ C)

  -- The four well-known coherence laws for symmetric monoidal categories

  *-pentagon : ∀ A B C D →
    Path (((A * B) * C) * D ≡ A * (B * (C * D)))
      (*-assoc (A * B) C D ∙ *-assoc A B (C * D))
      (cong (_* D) (*-assoc A B C) ∙∙ *-assoc A (B * C) D ∙∙ cong (A *_) (*-assoc B C D))

  *-triangle : ∀ A B →
    Square
      (*-assoc A ⊤ B)
      (cong (_* B) (*-identityʳ A))
      refl
      (cong (A *_) (*-identityˡ B))

  *-hexagon : ∀ A B C →
    Path ((A * B) * C ≡ B * (C * A))
      (*-assoc A B C ∙∙ *-comm A (B * C) ∙∙ *-assoc B C A)
      (cong (_* C) (*-comm A B) ∙∙ *-assoc B A C ∙∙ cong (B *_) (*-comm A C))

  *-bigon : ∀ A B → *-comm A B ≡ sym (*-comm B A)

  -- A ⇒_ is a symmetric monoidal functor

  ⇒-*-identityˡ : ∀ A B →
    Square
      (cong (_* (A ⇒ B)) (⇒-annihilʳ A))
      (cong (A ⇒_) (*-identityˡ B))
      (sym (⇒-distribˡ A ⊤ B))
      (*-identityˡ (A ⇒ B))

  ⇒-*-identityʳ : ∀ A B →
    Square
      (cong ((A ⇒ B) *_) (⇒-annihilʳ A))
      (cong (A ⇒_) (*-identityʳ B))
      (sym (⇒-distribˡ A B ⊤))
      (*-identityʳ (A ⇒ B))

  ⇒-*-comm : ∀ A B C →
    Square
      (⇒-distribˡ A B C)
      (⇒-distribˡ A C B)
      (cong (A ⇒_) (*-comm B C))
      (*-comm (A ⇒ B) (A ⇒ C))

  ⇒-*-assoc : ∀ A B C D →
    Square
      (⇒-distribˡ A (B * C) D ∙ cong (_* (A ⇒ D)) (⇒-distribˡ A B C))
      (⇒-distribˡ A B (C * D) ∙ cong ((A ⇒ B) *_) (⇒-distribˡ A C D))
      (cong (A ⇒_) (*-assoc B C D))
      (*-assoc (A ⇒ B) (A ⇒ C) (A ⇒ D))

  -- interactions between ⇒-identityˡ, ⇒-curry, and SMC morphisms

  ⇒-curry-identityˡ : ∀ A B →
    Square
      (⇒-identityˡ (A ⇒ B))
      (sym (cong (_⇒ B) (*-identityˡ A)))
      refl
      (⇒-curry ⊤ A B)

  ⇒-curry-identityʳ : ∀ A B →
    Square
      (cong (A ⇒_) (⇒-identityˡ B))
      (sym (cong (_⇒ B) (*-identityʳ A)))
      refl
      (⇒-curry A ⊤ B)

  ⇒-curry-assoc : ∀ A B C D →
    Square
      (⇒-curry A B (C ⇒ D) ∙ ⇒-curry (A * B) C D)
      (cong (A ⇒_) (⇒-curry B C D) ∙ ⇒-curry A (B * C) D)
      refl
      (cong (_⇒ D) (*-assoc A B C))

  -- TODO: Are these coherence laws really needed? Are there any missing ones?

  -- only groupoid truncate to allow interpretation into hSet
  trunc : ∀ A B (p q : A ≡ B) (P Q : p ≡ q) → P ≡ Q

--------------------------------------------------------------------------------
-- Eliminators

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

compPathP'≡compPath : ∀ {a} {A : Type a} {x y z : A} →
  (p : x ≡ y) (q : y ≡ z) →
  compPathP' {p = p} {q = q} p q ≡ p ∙ q
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

private
  variable
    A B C D : Ty n

record Model ℓ : Type (ℓ-suc ℓ) where
  no-eta-equality
  infixr 5 _⇒ᴹ_
  infixr 6 _*ᴹ_
  field
    Tyᴹ : ℕ → Type ℓ
    isGroupoidTyᴹ : isGroupoid (Tyᴹ n)

    ιᴹ : Fin n → Tyᴹ n
    ⊤ᴹ : Tyᴹ n
    _*ᴹ_ : Tyᴹ n → Tyᴹ n → Tyᴹ n
    _⇒ᴹ_ : Tyᴹ n → Tyᴹ n → Tyᴹ n

    *-identityˡᴹ : (A : Tyᴹ n) → ⊤ᴹ *ᴹ A ≡ A
    *-identityʳᴹ : (A : Tyᴹ n) → A *ᴹ ⊤ᴹ ≡ A
    *-commᴹ : (A : Tyᴹ n) (B : Tyᴹ n) → A *ᴹ B ≡ B *ᴹ A
    *-assocᴹ : (A : Tyᴹ n) (B : Tyᴹ n) (C : Tyᴹ n) → (A *ᴹ B) *ᴹ C ≡ A *ᴹ (B *ᴹ C)

    ⇒-identityˡᴹ : (A : Tyᴹ n) → A ≡ ⊤ᴹ ⇒ᴹ A
    ⇒-curryᴹ : (A : Tyᴹ n) (B : Tyᴹ n) (C : Tyᴹ n) → A ⇒ᴹ (B ⇒ᴹ C) ≡ (A *ᴹ B) ⇒ᴹ C
    ⇒-annihilʳᴹ : (A : Tyᴹ n) → A ⇒ᴹ ⊤ᴹ ≡ ⊤ᴹ
    ⇒-distribˡᴹ : (A : Tyᴹ n) (B : Tyᴹ n) (C : Tyᴹ n) → A ⇒ᴹ (B *ᴹ C) ≡ (A ⇒ᴹ B) *ᴹ (A ⇒ᴹ C)

    *-pentagonᴹ : (Aᴹ : Tyᴹ n) (Bᴹ : Tyᴹ n) (Cᴹ : Tyᴹ n) (Dᴹ : Tyᴹ n) →
      Path (((Aᴹ *ᴹ Bᴹ) *ᴹ Cᴹ) *ᴹ Dᴹ ≡ Aᴹ *ᴹ (Bᴹ *ᴹ (Cᴹ *ᴹ Dᴹ)))
        (*-assocᴹ (Aᴹ *ᴹ Bᴹ) Cᴹ Dᴹ ∙ *-assocᴹ Aᴹ Bᴹ (Cᴹ *ᴹ Dᴹ))
        (cong (_*ᴹ Dᴹ) (*-assocᴹ Aᴹ Bᴹ Cᴹ) ∙∙ *-assocᴹ Aᴹ (Bᴹ *ᴹ Cᴹ) Dᴹ ∙∙ cong (Aᴹ *ᴹ_) (*-assocᴹ Bᴹ Cᴹ Dᴹ))

    *-triangleᴹ : (Aᴹ : Tyᴹ n) (Bᴹ : Tyᴹ n) →
      Square (*-assocᴹ Aᴹ ⊤ᴹ Bᴹ)
        (cong (_*ᴹ Bᴹ) (*-identityʳᴹ Aᴹ))
        refl
        (cong (Aᴹ *ᴹ_) (*-identityˡᴹ Bᴹ))

    *-hexagonᴹ : (Aᴹ : Tyᴹ n) (Bᴹ : Tyᴹ n) (Cᴹ : Tyᴹ n) →
      Path ((Aᴹ *ᴹ Bᴹ) *ᴹ Cᴹ ≡ Bᴹ *ᴹ (Cᴹ *ᴹ Aᴹ))
        (*-assocᴹ Aᴹ Bᴹ Cᴹ ∙∙ *-commᴹ Aᴹ (Bᴹ *ᴹ Cᴹ) ∙∙ *-assocᴹ Bᴹ Cᴹ Aᴹ)
        (cong (_*ᴹ Cᴹ) (*-commᴹ Aᴹ Bᴹ) ∙∙ *-assocᴹ Bᴹ Aᴹ Cᴹ ∙∙ cong (Bᴹ *ᴹ_) (*-commᴹ Aᴹ Cᴹ))

    *-bigonᴹ : (Aᴹ : Tyᴹ n) (Bᴹ : Tyᴹ n) → *-commᴹ Aᴹ Bᴹ ≡ sym (*-commᴹ Bᴹ Aᴹ)

    ⇒-*-identityˡᴹ : (Aᴹ : Tyᴹ n) (Bᴹ : Tyᴹ n) →
      Square
        (cong (_*ᴹ (Aᴹ ⇒ᴹ Bᴹ)) (⇒-annihilʳᴹ Aᴹ))
        (cong (Aᴹ ⇒ᴹ_) (*-identityˡᴹ Bᴹ))
        (sym (⇒-distribˡᴹ Aᴹ ⊤ᴹ Bᴹ))
        (*-identityˡᴹ (Aᴹ ⇒ᴹ Bᴹ))

    ⇒-*-identityʳᴹ : (Aᴹ : Tyᴹ n) (Bᴹ : Tyᴹ n) →
      Square
        (cong ((Aᴹ ⇒ᴹ Bᴹ) *ᴹ_) (⇒-annihilʳᴹ Aᴹ))
        (cong (Aᴹ ⇒ᴹ_) (*-identityʳᴹ Bᴹ))
        (sym (⇒-distribˡᴹ Aᴹ Bᴹ ⊤ᴹ))
        (*-identityʳᴹ (Aᴹ ⇒ᴹ Bᴹ))

    ⇒-*-commᴹ : (Aᴹ : Tyᴹ n) (Bᴹ : Tyᴹ n) (Cᴹ : Tyᴹ n) →
      Square
        (⇒-distribˡᴹ Aᴹ Bᴹ Cᴹ)
        (⇒-distribˡᴹ Aᴹ Cᴹ Bᴹ)
        (cong (Aᴹ ⇒ᴹ_) (*-commᴹ Bᴹ Cᴹ))
        (*-commᴹ (Aᴹ ⇒ᴹ Bᴹ) (Aᴹ ⇒ᴹ Cᴹ))

    ⇒-*-assocᴹ : (Aᴹ : Tyᴹ n) (Bᴹ : Tyᴹ n) (Cᴹ : Tyᴹ n) (Dᴹ : Tyᴹ n) →
      Square
        (⇒-distribˡᴹ Aᴹ (Bᴹ *ᴹ Cᴹ) Dᴹ ∙ cong (_*ᴹ (Aᴹ ⇒ᴹ Dᴹ)) (⇒-distribˡᴹ Aᴹ Bᴹ Cᴹ))
        (⇒-distribˡᴹ Aᴹ Bᴹ (Cᴹ *ᴹ Dᴹ) ∙ cong ((Aᴹ ⇒ᴹ Bᴹ) *ᴹ_) (⇒-distribˡᴹ Aᴹ Cᴹ Dᴹ))
        (cong (Aᴹ ⇒ᴹ_) (*-assocᴹ Bᴹ Cᴹ Dᴹ))
        (*-assocᴹ (Aᴹ ⇒ᴹ Bᴹ) (Aᴹ ⇒ᴹ Cᴹ) (Aᴹ ⇒ᴹ Dᴹ))

    ⇒-curry-identityˡᴹ : (Aᴹ : Tyᴹ n) (Bᴹ : Tyᴹ n) →
      Square
        (⇒-identityˡᴹ (Aᴹ ⇒ᴹ Bᴹ))
        (sym (cong (_⇒ᴹ Bᴹ) (*-identityˡᴹ Aᴹ)))
        refl
        (⇒-curryᴹ ⊤ᴹ Aᴹ Bᴹ)

    ⇒-curry-identityʳᴹ : (Aᴹ : Tyᴹ n) (Bᴹ : Tyᴹ n) →
      Square
        (cong (Aᴹ ⇒ᴹ_) (⇒-identityˡᴹ Bᴹ))
        (sym (cong (_⇒ᴹ Bᴹ) (*-identityʳᴹ Aᴹ)))
        refl
        (⇒-curryᴹ Aᴹ ⊤ᴹ Bᴹ)

    ⇒-curry-assocᴹ : (Aᴹ : Tyᴹ n) (Bᴹ : Tyᴹ n) (Cᴹ : Tyᴹ n) (Dᴹ : Tyᴹ n) →
      Square
        (⇒-curryᴹ Aᴹ Bᴹ (Cᴹ ⇒ᴹ Dᴹ) ∙ ⇒-curryᴹ (Aᴹ *ᴹ Bᴹ) Cᴹ Dᴹ)
        (cong (Aᴹ ⇒ᴹ_) (⇒-curryᴹ Bᴹ Cᴹ Dᴹ) ∙ ⇒-curryᴹ Aᴹ (Bᴹ *ᴹ Cᴹ) Dᴹ)
        refl
        (cong (_⇒ᴹ Dᴹ) (*-assocᴹ Aᴹ Bᴹ Cᴹ))

module Rec {ℓ} (M : Model ℓ) where
  open Model M

  ⟦_⟧ : Ty n → Tyᴹ n
  ⟦ ι x ⟧ = ιᴹ x
  ⟦ ⊤ ⟧ = ⊤ᴹ
  ⟦ A * B ⟧ = ⟦ A ⟧ *ᴹ ⟦ B ⟧
  ⟦ A ⇒ B ⟧ = ⟦ A ⟧ ⇒ᴹ ⟦ B ⟧
  ⟦ *-identityˡ A i ⟧ = *-identityˡᴹ ⟦ A ⟧ i
  ⟦ *-identityʳ A i ⟧ = *-identityʳᴹ ⟦ A ⟧ i
  ⟦ *-comm A B i ⟧ = *-commᴹ ⟦ A ⟧ ⟦ B ⟧ i
  ⟦ *-assoc A B C i ⟧ = *-assocᴹ ⟦ A ⟧ ⟦ B ⟧ ⟦ C ⟧ i
  ⟦ ⇒-identityˡ A i ⟧ = ⇒-identityˡᴹ ⟦ A ⟧ i
  ⟦ ⇒-curry A B C i ⟧ = ⇒-curryᴹ ⟦ A ⟧ ⟦ B ⟧ ⟦ C ⟧ i
  ⟦ ⇒-annihilʳ A i ⟧ = ⇒-annihilʳᴹ ⟦ A ⟧ i
  ⟦ ⇒-distribˡ A B C i ⟧ = ⇒-distribˡᴹ ⟦ A ⟧ ⟦ B ⟧ ⟦ C ⟧ i
  ⟦ *-pentagon A B C D i j ⟧ =
    (compPathP'≡compPath _ _
      ∙∙ *-pentagonᴹ ⟦ A ⟧ ⟦ B ⟧ ⟦ C ⟧ ⟦ D ⟧
      ∙∙ sym (doubleCompPathP≡doubleCompPath _ _ _))
    i j
  ⟦ *-triangle A B i j ⟧ = *-triangleᴹ ⟦ A ⟧ ⟦ B ⟧ i j
  ⟦ *-hexagon A B C i j ⟧ =
    (doubleCompPathP≡doubleCompPath _ _ _
      ∙∙ *-hexagonᴹ ⟦ A ⟧ ⟦ B ⟧ ⟦ C ⟧
      ∙∙ sym (doubleCompPathP≡doubleCompPath _ _ _))
    i j
  ⟦ *-bigon A B i j ⟧ = *-bigonᴹ ⟦ A ⟧ ⟦ B ⟧ i j
  ⟦ ⇒-*-identityˡ A B i j ⟧ = ⇒-*-identityˡᴹ ⟦ A ⟧ ⟦ B ⟧ i j
  ⟦ ⇒-*-identityʳ A B i j ⟧ = ⇒-*-identityʳᴹ ⟦ A ⟧ ⟦ B ⟧ i j
  ⟦ ⇒-*-comm A B C i j ⟧ = ⇒-*-commᴹ ⟦ A ⟧ ⟦ B ⟧ ⟦ C ⟧ i j
  ⟦ ⇒-*-assoc A B C D i j ⟧ =
    (compPathP'≡compPath _ _
      ◁ ⇒-*-assocᴹ ⟦ A ⟧ ⟦ B ⟧ ⟦ C ⟧ ⟦ D ⟧ ▷
      sym (compPathP'≡compPath _ _))
    i j
  ⟦ ⇒-curry-identityˡ A B i j ⟧ = ⇒-curry-identityˡᴹ ⟦ A ⟧ ⟦ B ⟧ i j
  ⟦ ⇒-curry-identityʳ A B i j ⟧ = ⇒-curry-identityʳᴹ ⟦ A ⟧ ⟦ B ⟧ i j
  ⟦ ⇒-curry-assoc A B C D i j ⟧ =
    (compPathP'≡compPath _ _
      ◁ ⇒-curry-assocᴹ ⟦ A ⟧ ⟦ B ⟧ ⟦ C ⟧ ⟦ D ⟧ ▷
      sym (compPathP'≡compPath _ _))
    i j
  ⟦ trunc A B p q P Q i j k ⟧ =
    isGroupoidTyᴹ
      ⟦ A ⟧ ⟦ B ⟧
      (λ i → ⟦ p i ⟧) (λ i → ⟦ q i ⟧)
      (λ i j → ⟦ P i j ⟧) (λ i j → ⟦ Q i j ⟧)
      i j k


record ModelDepSet ℓ : Type (ℓ-suc ℓ) where
  no-eta-equality
  infixr 5 _⇒ᴹ_
  infixr 6 _*ᴹ_
  field
    Tyᴹ : Ty n → Type ℓ
    isSetTyᴹ : (A : Ty n) → isSet (Tyᴹ A)

    ιᴹ : (x : Fin n) → Tyᴹ (ι x)
    ⊤ᴹ : Tyᴹ {n = n} ⊤
    _*ᴹ_ : (Aᴹ : Tyᴹ A) (Bᴹ : Tyᴹ B) → Tyᴹ (A * B)
    _⇒ᴹ_ : (Aᴹ : Tyᴹ A) (Bᴹ : Tyᴹ B) → Tyᴹ (A ⇒ B)

    *-identityˡᴹ : (Aᴹ : Tyᴹ A) →
      PathP (λ i → Tyᴹ (*-identityˡ A i)) (⊤ᴹ *ᴹ Aᴹ) Aᴹ
    *-identityʳᴹ : (Aᴹ : Tyᴹ A) →
      PathP (λ i → Tyᴹ (*-identityʳ A i)) (Aᴹ *ᴹ ⊤ᴹ) Aᴹ
    *-commᴹ : (Aᴹ : Tyᴹ A) (Bᴹ : Tyᴹ B) →
      PathP (λ i → Tyᴹ (*-comm A B i)) (Aᴹ *ᴹ Bᴹ) (Bᴹ *ᴹ Aᴹ)
    *-assocᴹ : (Aᴹ : Tyᴹ A) (Bᴹ : Tyᴹ B) (Cᴹ : Tyᴹ C) →
      PathP (λ i → Tyᴹ (*-assoc A B C i)) ((Aᴹ *ᴹ Bᴹ) *ᴹ Cᴹ) (Aᴹ *ᴹ (Bᴹ *ᴹ Cᴹ))

    ⇒-identityˡᴹ : (Aᴹ : Tyᴹ A) →
      PathP (λ i → Tyᴹ (⇒-identityˡ A i)) Aᴹ (⊤ᴹ ⇒ᴹ Aᴹ)
    ⇒-curryᴹ : (Aᴹ : Tyᴹ A) (Bᴹ : Tyᴹ B) (Cᴹ : Tyᴹ C) →
      PathP (λ i → Tyᴹ (⇒-curry A B C i)) (Aᴹ ⇒ᴹ (Bᴹ ⇒ᴹ Cᴹ)) ((Aᴹ *ᴹ Bᴹ) ⇒ᴹ Cᴹ)
    ⇒-annihilʳᴹ : (Aᴹ : Tyᴹ A) →
      PathP (λ i → Tyᴹ (⇒-annihilʳ A i)) (Aᴹ ⇒ᴹ ⊤ᴹ) ⊤ᴹ
    ⇒-distribˡᴹ : (Aᴹ : Tyᴹ A) (Bᴹ : Tyᴹ B) (Cᴹ : Tyᴹ C) →
      PathP (λ i → Tyᴹ (⇒-distribˡ A B C i)) (Aᴹ ⇒ᴹ (Bᴹ *ᴹ Cᴹ)) ((Aᴹ ⇒ᴹ Bᴹ) *ᴹ (Aᴹ ⇒ᴹ Cᴹ))

  *-pentagonᴹ : (Aᴹ : Tyᴹ A) (Bᴹ : Tyᴹ B) (Cᴹ : Tyᴹ C) (Dᴹ : Tyᴹ D) →
    SquareP (λ i j → Tyᴹ (*-pentagon A B C D i j))
      (compPathP' {B = Tyᴹ}
        (*-assocᴹ (Aᴹ *ᴹ Bᴹ) Cᴹ Dᴹ)
        (*-assocᴹ Aᴹ Bᴹ (Cᴹ *ᴹ Dᴹ)))
      (doubleCompPathP {B = Tyᴹ}
        (congP (λ _ → _*ᴹ Dᴹ) (*-assocᴹ Aᴹ Bᴹ Cᴹ))
        (*-assocᴹ Aᴹ (Bᴹ *ᴹ Cᴹ) Dᴹ)
        (congP (λ _ → Aᴹ *ᴹ_) (*-assocᴹ Bᴹ Cᴹ Dᴹ)))
      refl
      refl
  *-pentagonᴹ {A = A} {B = B} {C = C} {D = D} Aᴹ Bᴹ Cᴹ Dᴹ =
    isSet→SquareP
      (λ i j → isSetTyᴹ (*-pentagon A B C D i j))
      (compPathP' {B = Tyᴹ}
        (*-assocᴹ (Aᴹ *ᴹ Bᴹ) Cᴹ Dᴹ)
        (*-assocᴹ Aᴹ Bᴹ (Cᴹ *ᴹ Dᴹ)))
      (doubleCompPathP {B = Tyᴹ}
        (congP (λ _ → _*ᴹ Dᴹ) (*-assocᴹ Aᴹ Bᴹ Cᴹ))
        (*-assocᴹ Aᴹ (Bᴹ *ᴹ Cᴹ) Dᴹ)
        (congP (λ _ → Aᴹ *ᴹ_) (*-assocᴹ Bᴹ Cᴹ Dᴹ)))
      refl
      refl

  *-triangleᴹ : (Aᴹ : Tyᴹ A) (Bᴹ : Tyᴹ B) →
    SquareP (λ i j → Tyᴹ (*-triangle A B i j))
      (*-assocᴹ Aᴹ ⊤ᴹ Bᴹ)
      (congP (λ _ → _*ᴹ Bᴹ) (*-identityʳᴹ Aᴹ))
      refl
      (congP (λ _ → Aᴹ *ᴹ_) (*-identityˡᴹ Bᴹ))
  *-triangleᴹ {A = A} {B = B} Aᴹ Bᴹ =
    isSet→SquareP
      (λ i j → isSetTyᴹ (*-triangle A B i j))
      (*-assocᴹ Aᴹ ⊤ᴹ Bᴹ)
      (congP (λ _ → _*ᴹ Bᴹ) (*-identityʳᴹ Aᴹ))
      refl
      (congP (λ _ → Aᴹ *ᴹ_) (*-identityˡᴹ Bᴹ))

  *-hexagonᴹ : (Aᴹ : Tyᴹ A) (Bᴹ : Tyᴹ B) (Cᴹ : Tyᴹ C) →
    SquareP (λ i j → Tyᴹ (*-hexagon A B C i j))
      (doubleCompPathP {B = Tyᴹ}
        (*-assocᴹ Aᴹ Bᴹ Cᴹ)
        (*-commᴹ Aᴹ (Bᴹ *ᴹ Cᴹ))
        (*-assocᴹ Bᴹ Cᴹ Aᴹ))
      (doubleCompPathP {B = Tyᴹ}
        (congP (λ _ → _*ᴹ Cᴹ) (*-commᴹ Aᴹ Bᴹ))
        (*-assocᴹ Bᴹ Aᴹ Cᴹ)
        (congP (λ _ → Bᴹ *ᴹ_) (*-commᴹ Aᴹ Cᴹ)))
      refl
      refl
  *-hexagonᴹ {A = A} {B = B} {C = C} Aᴹ Bᴹ Cᴹ =
    isSet→SquareP
      (λ i j → isSetTyᴹ (*-hexagon A B C i j))
      (doubleCompPathP {B = Tyᴹ}
        (*-assocᴹ Aᴹ Bᴹ Cᴹ)
        (*-commᴹ Aᴹ (Bᴹ *ᴹ Cᴹ))
        (*-assocᴹ Bᴹ Cᴹ Aᴹ))
      (doubleCompPathP {B = Tyᴹ}
        (congP (λ _ → _*ᴹ Cᴹ) (*-commᴹ Aᴹ Bᴹ))
        (*-assocᴹ Bᴹ Aᴹ Cᴹ)
        (congP (λ _ → Bᴹ *ᴹ_) (*-commᴹ Aᴹ Cᴹ)))
      refl
      refl

  *-bigonᴹ : (Aᴹ : Tyᴹ A) (Bᴹ : Tyᴹ B) →
    SquareP (λ i j → Tyᴹ (*-bigon A B i j))
      (*-commᴹ Aᴹ Bᴹ)
      (symP (*-commᴹ Bᴹ Aᴹ))
      refl
      refl
  *-bigonᴹ {A = A} {B = B} Aᴹ Bᴹ =
    isSet→SquareP
      (λ i j → isSetTyᴹ (*-bigon A B i j))
      (*-commᴹ Aᴹ Bᴹ)
      (symP (*-commᴹ Bᴹ Aᴹ))
      refl
      refl

  ⇒-*-identityˡᴹ : (Aᴹ : Tyᴹ A) (Bᴹ : Tyᴹ B) →
    SquareP (λ i j → Tyᴹ (⇒-*-identityˡ A B i j))
      (congP (λ _ → _*ᴹ (Aᴹ ⇒ᴹ Bᴹ)) (⇒-annihilʳᴹ Aᴹ))
      (congP (λ _ → Aᴹ ⇒ᴹ_) (*-identityˡᴹ Bᴹ))
      (symP (⇒-distribˡᴹ Aᴹ ⊤ᴹ Bᴹ))
      (*-identityˡᴹ (Aᴹ ⇒ᴹ Bᴹ))
  ⇒-*-identityˡᴹ {A = A} {B = B} Aᴹ Bᴹ =
    isSet→SquareP
      (λ i j → isSetTyᴹ (⇒-*-identityˡ A B i j))
      (congP (λ _ → _*ᴹ (Aᴹ ⇒ᴹ Bᴹ)) (⇒-annihilʳᴹ Aᴹ))
      (congP (λ _ → Aᴹ ⇒ᴹ_) (*-identityˡᴹ Bᴹ))
      (symP (⇒-distribˡᴹ Aᴹ ⊤ᴹ Bᴹ))
      (*-identityˡᴹ (Aᴹ ⇒ᴹ Bᴹ))

  ⇒-*-identityʳᴹ : (Aᴹ : Tyᴹ A) (Bᴹ : Tyᴹ B) →
    SquareP (λ i j → Tyᴹ (⇒-*-identityʳ A B i j))
      (congP (λ _ → (Aᴹ ⇒ᴹ Bᴹ) *ᴹ_) (⇒-annihilʳᴹ Aᴹ))
      (congP (λ _ → Aᴹ ⇒ᴹ_) (*-identityʳᴹ Bᴹ))
      (symP (⇒-distribˡᴹ Aᴹ Bᴹ ⊤ᴹ))
      (*-identityʳᴹ (Aᴹ ⇒ᴹ Bᴹ))
  ⇒-*-identityʳᴹ {A = A} {B = B} Aᴹ Bᴹ =
    isSet→SquareP
      (λ i j → isSetTyᴹ (⇒-*-identityʳ A B i j))
      (congP (λ _ → (Aᴹ ⇒ᴹ Bᴹ) *ᴹ_) (⇒-annihilʳᴹ Aᴹ))
      (congP (λ _ → Aᴹ ⇒ᴹ_) (*-identityʳᴹ Bᴹ))
      (symP (⇒-distribˡᴹ Aᴹ Bᴹ ⊤ᴹ))
      (*-identityʳᴹ (Aᴹ ⇒ᴹ Bᴹ))

  ⇒-*-commᴹ : (Aᴹ : Tyᴹ A) (Bᴹ : Tyᴹ B) (Cᴹ : Tyᴹ C) →
    SquareP (λ i j → Tyᴹ (⇒-*-comm A B C i j))
      (⇒-distribˡᴹ Aᴹ Bᴹ Cᴹ)
      (⇒-distribˡᴹ Aᴹ Cᴹ Bᴹ)
      (congP (λ _ → Aᴹ ⇒ᴹ_) (*-commᴹ Bᴹ Cᴹ))
      (*-commᴹ (Aᴹ ⇒ᴹ Bᴹ) (Aᴹ ⇒ᴹ Cᴹ))
  ⇒-*-commᴹ {A = A} {B = B} {C = C} Aᴹ Bᴹ Cᴹ =
    isSet→SquareP
      (λ i j → isSetTyᴹ (⇒-*-comm A B C i j))
      (⇒-distribˡᴹ Aᴹ Bᴹ Cᴹ)
      (⇒-distribˡᴹ Aᴹ Cᴹ Bᴹ)
      (congP (λ _ → Aᴹ ⇒ᴹ_) (*-commᴹ Bᴹ Cᴹ))
      (*-commᴹ (Aᴹ ⇒ᴹ Bᴹ) (Aᴹ ⇒ᴹ Cᴹ))

  ⇒-*-assocᴹ : (Aᴹ : Tyᴹ A) (Bᴹ : Tyᴹ B) (Cᴹ : Tyᴹ C) (Dᴹ : Tyᴹ D) →
    SquareP (λ i j → Tyᴹ (⇒-*-assoc A B C D i j))
      (compPathP' {B = Tyᴹ}
        (⇒-distribˡᴹ Aᴹ (Bᴹ *ᴹ Cᴹ) Dᴹ)
        (congP (λ _ → _*ᴹ (Aᴹ ⇒ᴹ Dᴹ)) (⇒-distribˡᴹ Aᴹ Bᴹ Cᴹ)))
      (compPathP' {B = Tyᴹ}
        (⇒-distribˡᴹ Aᴹ Bᴹ (Cᴹ *ᴹ Dᴹ))
        (congP (λ _ → (Aᴹ ⇒ᴹ Bᴹ) *ᴹ_) (⇒-distribˡᴹ Aᴹ Cᴹ Dᴹ)))
      (congP (λ _ → Aᴹ ⇒ᴹ_) (*-assocᴹ Bᴹ Cᴹ Dᴹ))
      (*-assocᴹ (Aᴹ ⇒ᴹ Bᴹ) (Aᴹ ⇒ᴹ Cᴹ) (Aᴹ ⇒ᴹ Dᴹ))
  ⇒-*-assocᴹ {A = A} {B = B} {C = C} {D = D} Aᴹ Bᴹ Cᴹ Dᴹ =
    isSet→SquareP
      (λ i j → isSetTyᴹ (⇒-*-assoc A B C D i j))
      (compPathP' {B = Tyᴹ}
        (⇒-distribˡᴹ Aᴹ (Bᴹ *ᴹ Cᴹ) Dᴹ)
        (congP (λ _ → _*ᴹ (Aᴹ ⇒ᴹ Dᴹ)) (⇒-distribˡᴹ Aᴹ Bᴹ Cᴹ)))
      (compPathP' {B = Tyᴹ}
        (⇒-distribˡᴹ Aᴹ Bᴹ (Cᴹ *ᴹ Dᴹ))
        (congP (λ _ → (Aᴹ ⇒ᴹ Bᴹ) *ᴹ_) (⇒-distribˡᴹ Aᴹ Cᴹ Dᴹ)))
      (congP (λ _ → Aᴹ ⇒ᴹ_) (*-assocᴹ Bᴹ Cᴹ Dᴹ))
      (*-assocᴹ (Aᴹ ⇒ᴹ Bᴹ) (Aᴹ ⇒ᴹ Cᴹ) (Aᴹ ⇒ᴹ Dᴹ))

  ⇒-curry-identityˡᴹ : (Aᴹ : Tyᴹ A) (Bᴹ : Tyᴹ B) →
    SquareP (λ i j → Tyᴹ (⇒-curry-identityˡ A B i j))
      (⇒-identityˡᴹ (Aᴹ ⇒ᴹ Bᴹ))
      (symP (congP (λ _ → _⇒ᴹ Bᴹ) (*-identityˡᴹ Aᴹ)))
      refl
      (⇒-curryᴹ ⊤ᴹ Aᴹ Bᴹ)
  ⇒-curry-identityˡᴹ {A = A} {B = B} Aᴹ Bᴹ =
    isSet→SquareP
      (λ i j → isSetTyᴹ (⇒-curry-identityˡ A B i j))
      (⇒-identityˡᴹ (Aᴹ ⇒ᴹ Bᴹ))
      (symP (congP (λ _ → _⇒ᴹ Bᴹ) (*-identityˡᴹ Aᴹ)))
      refl
      (⇒-curryᴹ ⊤ᴹ Aᴹ Bᴹ)

  ⇒-curry-identityʳᴹ : (Aᴹ : Tyᴹ A) (Bᴹ : Tyᴹ B) →
    SquareP (λ i j → Tyᴹ (⇒-curry-identityʳ A B i j))
      (congP (λ _ → Aᴹ ⇒ᴹ_) (⇒-identityˡᴹ Bᴹ))
      (symP (congP (λ _ → _⇒ᴹ Bᴹ) (*-identityʳᴹ Aᴹ)))
      refl
      (⇒-curryᴹ Aᴹ ⊤ᴹ Bᴹ)
  ⇒-curry-identityʳᴹ {A = A} {B = B} Aᴹ Bᴹ =
    isSet→SquareP
      (λ i j → isSetTyᴹ (⇒-curry-identityʳ A B i j))
      (congP (λ _ → Aᴹ ⇒ᴹ_) (⇒-identityˡᴹ Bᴹ))
      (symP (congP (λ _ → _⇒ᴹ Bᴹ) (*-identityʳᴹ Aᴹ)))
      refl
      (⇒-curryᴹ Aᴹ ⊤ᴹ Bᴹ)

  ⇒-curry-assocᴹ : (Aᴹ : Tyᴹ A) (Bᴹ : Tyᴹ B) (Cᴹ : Tyᴹ C) (Dᴹ : Tyᴹ D) →
    SquareP (λ i j → Tyᴹ (⇒-curry-assoc A B C D i j))
      (compPathP' {B = Tyᴹ}
        (⇒-curryᴹ Aᴹ Bᴹ (Cᴹ ⇒ᴹ Dᴹ))
        (⇒-curryᴹ (Aᴹ *ᴹ Bᴹ) Cᴹ Dᴹ))
      (compPathP' {B = Tyᴹ}
        (congP (λ _ → Aᴹ ⇒ᴹ_) (⇒-curryᴹ Bᴹ Cᴹ Dᴹ))
        (⇒-curryᴹ Aᴹ (Bᴹ *ᴹ Cᴹ) Dᴹ))
      refl
      (congP (λ _ → _⇒ᴹ Dᴹ) (*-assocᴹ Aᴹ Bᴹ Cᴹ))
  ⇒-curry-assocᴹ {A = A} {B = B} {C = C} {D = D} Aᴹ Bᴹ Cᴹ Dᴹ =
    isSet→SquareP
      (λ i j → isSetTyᴹ (⇒-curry-assoc A B C D i j))
      (compPathP' {B = Tyᴹ}
        (⇒-curryᴹ Aᴹ Bᴹ (Cᴹ ⇒ᴹ Dᴹ))
        (⇒-curryᴹ (Aᴹ *ᴹ Bᴹ) Cᴹ Dᴹ))
      (compPathP' {B = Tyᴹ}
        (congP (λ _ → Aᴹ ⇒ᴹ_) (⇒-curryᴹ Bᴹ Cᴹ Dᴹ))
        (⇒-curryᴹ Aᴹ (Bᴹ *ᴹ Cᴹ) Dᴹ))
      refl
      (congP (λ _ → _⇒ᴹ Dᴹ) (*-assocᴹ Aᴹ Bᴹ Cᴹ))

module ElimSet {ℓ} (M : ModelDepSet ℓ) where
  open ModelDepSet M

  ⟦_⟧ : (A : Ty n) → Tyᴹ A
  ⟦ ι x ⟧ = ιᴹ x
  ⟦ ⊤ ⟧ = ⊤ᴹ
  ⟦ A * B ⟧ = ⟦ A ⟧ *ᴹ ⟦ B ⟧
  ⟦ A ⇒ B ⟧ = ⟦ A ⟧ ⇒ᴹ ⟦ B ⟧
  ⟦ *-identityˡ A i ⟧ = *-identityˡᴹ ⟦ A ⟧ i
  ⟦ *-identityʳ A i ⟧ = *-identityʳᴹ ⟦ A ⟧ i
  ⟦ *-comm A B i ⟧ = *-commᴹ ⟦ A ⟧ ⟦ B ⟧ i
  ⟦ *-assoc A B C i ⟧ = *-assocᴹ ⟦ A ⟧ ⟦ B ⟧ ⟦ C ⟧ i
  ⟦ ⇒-identityˡ A i ⟧ = ⇒-identityˡᴹ ⟦ A ⟧ i
  ⟦ ⇒-curry A B C i ⟧ = ⇒-curryᴹ ⟦ A ⟧ ⟦ B ⟧ ⟦ C ⟧ i
  ⟦ ⇒-annihilʳ A i ⟧ = ⇒-annihilʳᴹ ⟦ A ⟧ i
  ⟦ ⇒-distribˡ A B C i ⟧ = ⇒-distribˡᴹ ⟦ A ⟧ ⟦ B ⟧ ⟦ C ⟧ i
  ⟦ *-pentagon A B C D i j ⟧ = *-pentagonᴹ ⟦ A ⟧ ⟦ B ⟧ ⟦ C ⟧ ⟦ D ⟧ i j
  ⟦ *-triangle A B i j ⟧ = *-triangleᴹ ⟦ A ⟧ ⟦ B ⟧ i j
  ⟦ *-hexagon A B C i j ⟧ = *-hexagonᴹ ⟦ A ⟧ ⟦ B ⟧ ⟦ C ⟧ i j
  ⟦ *-bigon A B i j ⟧ = *-bigonᴹ ⟦ A ⟧ ⟦ B ⟧ i j
  ⟦ ⇒-*-identityˡ A B i j ⟧ = ⇒-*-identityˡᴹ ⟦ A ⟧ ⟦ B ⟧ i j
  ⟦ ⇒-*-identityʳ A B i j ⟧ = ⇒-*-identityʳᴹ ⟦ A ⟧ ⟦ B ⟧ i j
  ⟦ ⇒-*-comm A B C i j ⟧ = ⇒-*-commᴹ ⟦ A ⟧ ⟦ B ⟧ ⟦ C ⟧ i j
  ⟦ ⇒-*-assoc A B C D i j ⟧ = ⇒-*-assocᴹ ⟦ A ⟧ ⟦ B ⟧ ⟦ C ⟧ ⟦ D ⟧ i j
  ⟦ ⇒-curry-identityˡ A B i j ⟧ = ⇒-curry-identityˡᴹ ⟦ A ⟧ ⟦ B ⟧ i j
  ⟦ ⇒-curry-identityʳ A B i j ⟧ = ⇒-curry-identityʳᴹ ⟦ A ⟧ ⟦ B ⟧ i j
  ⟦ ⇒-curry-assoc A B C D i j ⟧ = ⇒-curry-assocᴹ ⟦ A ⟧ ⟦ B ⟧ ⟦ C ⟧ ⟦ D ⟧ i j
  ⟦ trunc A B p q P Q i j k ⟧ =
    isGroupoid→CubeP
      (λ i j k → Tyᴹ (trunc A B p q P Q i j k))
      (λ j k → ⟦ P j k ⟧)
      (λ j k → ⟦ Q j k ⟧)
      (λ i k → ⟦ p k ⟧)
      (λ i k → ⟦ q k ⟧)
      (λ i j → ⟦ A ⟧)
      (λ i j → ⟦ B ⟧)
      (isSet→isGroupoid (isSetTyᴹ _))
      i j k
