module CartesianClosedCore.Free where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels using
  (isGroupoid→CubeP; isSet→SquareP; isSet→isGroupoid)

open import Cubical.Foundations.Extra using
  (doubleCompPathP; doubleCompPathP≡doubleCompPath; compPathP'≡compPath)

open import SymmetricMonoidalGroupoid.Structure

private
  variable
    ℓ : Level
    A : Type ℓ

infixr 5 _⇒_
infixr 6 _*_

--------------------------------------------------------------------------------

data Free (A : Type ℓ) : Type ℓ where
  ι : (x : A) → Free A
  ⊤ : Free A
  _*_ : (t u : Free A) → Free A
  _⇒_ : (t u : Free A) → Free A

  *-identityˡ : ∀ t → ⊤ * t ≡ t
  *-identityʳ : ∀ t → t * ⊤ ≡ t
  *-comm : ∀ t u → t * u ≡ u * t
  *-assoc : ∀ t u v → (t * u) * v ≡ t * (u * v)

  ⇒-identityˡ : ∀ t → t ≡ ⊤ ⇒ t
  ⇒-curry : ∀ t u v → t ⇒ u ⇒ v ≡ t * u ⇒ v
  ⇒-annihilʳ : ∀ t → t ⇒ ⊤ ≡ ⊤
  ⇒-distribˡ : ∀ t u v → t ⇒ u * v ≡ (t ⇒ u) * (t ⇒ v)

  *-bigon : ∀ t u → *-comm t u ≡ sym (*-comm u t)

  *-triangle : ∀ t u →
    Square
      (*-assoc t ⊤ u)
      (cong (_* u) (*-identityʳ t))
      refl
      (cong (t *_) (*-identityˡ u))

  *-pentagon : ∀ t u v w →
    Path (((t * u) * v) * w ≡ t * (u * (v * w)))
      (*-assoc (t * u) v w ∙ *-assoc t u (v * w))
      (cong (_* w) (*-assoc t u v)
        ∙∙ *-assoc t (u * v) w
        ∙∙ cong (t *_) (*-assoc u v w))

  *-hexagon : ∀ t u v →
    Path ((t * u) * v ≡ u * (v * t))
      (*-assoc t u v ∙∙ *-comm t (u * v) ∙∙ *-assoc u v t)
      (cong (_* v) (*-comm t u) ∙∙ *-assoc u t v ∙∙ cong (u *_) (*-comm t v))

  -- TODO: Add more coherence laws

  trunc : ∀ t u (p q : t ≡ u) (P Q : p ≡ q) → P ≡ Q

--------------------------------------------------------------------------------
-- Eliminators

record MotiveDep (A : Type ℓ) ℓ′ : Type (ℓ-suc (ℓ-max ℓ ℓ′)) where
  no-eta-equality
  infixr 5 _⇒ᴹ_
  infixr 6 _*ᴹ_
  field
    Freeᴹ : Free A → Type ℓ′
    isGroupoidFreeᴹ : ∀ t → isGroupoid (Freeᴹ t)
    ιᴹ : ∀ x → Freeᴹ (ι x)
    ⊤ᴹ : Freeᴹ ⊤
    _*ᴹ_ : ∀ {t u} (tᴹ : Freeᴹ t) (uᴹ : Freeᴹ u) → Freeᴹ (t * u)
    _⇒ᴹ_ : ∀ {t u} (tᴹ : Freeᴹ t) (uᴹ : Freeᴹ u) → Freeᴹ (t ⇒ u)

    *-identityˡᴹ : ∀ {t} tᴹ →
      PathP (λ i → Freeᴹ (*-identityˡ t i)) (⊤ᴹ *ᴹ tᴹ) tᴹ
    *-identityʳᴹ : ∀ {t} tᴹ →
      PathP (λ i → Freeᴹ (*-identityʳ t i)) (tᴹ *ᴹ ⊤ᴹ) tᴹ
    *-commᴹ : ∀ {t u} tᴹ uᴹ →
      PathP (λ i → Freeᴹ (*-comm t u i)) (tᴹ *ᴹ uᴹ) (uᴹ *ᴹ tᴹ)
    *-assocᴹ : ∀ {t u v} tᴹ uᴹ vᴹ →
      PathP (λ i → Freeᴹ (*-assoc t u v i))
        ((tᴹ *ᴹ uᴹ) *ᴹ vᴹ)
        (tᴹ *ᴹ (uᴹ *ᴹ vᴹ))

    ⇒-identityˡᴹ : ∀ {t} tᴹ →
      PathP (λ i → Freeᴹ (⇒-identityˡ t i)) tᴹ (⊤ᴹ ⇒ᴹ tᴹ)
    ⇒-curryᴹ : ∀ {t u v} tᴹ uᴹ vᴹ →
      PathP (λ i → Freeᴹ (⇒-curry t u v i))
        (tᴹ ⇒ᴹ uᴹ ⇒ᴹ vᴹ)
        (tᴹ *ᴹ uᴹ ⇒ᴹ vᴹ)
    ⇒-annihilʳᴹ : ∀ {t} tᴹ →
      PathP (λ i → Freeᴹ (⇒-annihilʳ t i)) (tᴹ ⇒ᴹ ⊤ᴹ) ⊤ᴹ
    ⇒-distribˡᴹ : ∀ {t u v} tᴹ uᴹ vᴹ →
      PathP (λ i → Freeᴹ (⇒-distribˡ t u v i))
        (tᴹ ⇒ᴹ uᴹ *ᴹ vᴹ)
        ((tᴹ ⇒ᴹ uᴹ) *ᴹ (tᴹ ⇒ᴹ vᴹ))

    *-bigonᴹ : ∀ {t u} tᴹ uᴹ →
      SquareP (λ i j → Freeᴹ (*-bigon t u i j))
        (*-commᴹ tᴹ uᴹ)
        (symP (*-commᴹ uᴹ tᴹ))
        refl
        refl

    *-triangleᴹ : ∀ {t u} tᴹ uᴹ →
      SquareP (λ i j → Freeᴹ (*-triangle t u i j))
        (*-assocᴹ tᴹ ⊤ᴹ uᴹ)
        (congP (λ _ → _*ᴹ uᴹ) (*-identityʳᴹ tᴹ))
        refl
        (congP (λ _ → tᴹ *ᴹ_) (*-identityˡᴹ uᴹ))

    *-pentagonᴹ : ∀ {t u v w} tᴹ uᴹ vᴹ wᴹ →
      SquareP (λ i j → Freeᴹ (*-pentagon t u v w i j))
        (compPathP' {B = Freeᴹ}
          (*-assocᴹ (tᴹ *ᴹ uᴹ) vᴹ wᴹ)
          (*-assocᴹ tᴹ uᴹ (vᴹ *ᴹ wᴹ)))
        (doubleCompPathP {B = Freeᴹ}
          (congP (λ _ → _*ᴹ wᴹ) (*-assocᴹ tᴹ uᴹ vᴹ))
          (*-assocᴹ tᴹ (uᴹ *ᴹ vᴹ) wᴹ)
          (congP (λ _ → tᴹ *ᴹ_) (*-assocᴹ uᴹ vᴹ wᴹ)))
        refl
        refl

    *-hexagonᴹ : ∀ {t u v} tᴹ uᴹ vᴹ →
      SquareP (λ i j → Freeᴹ (*-hexagon t u v i j))
        (doubleCompPathP {B = Freeᴹ}
          (*-assocᴹ tᴹ uᴹ vᴹ)
          (*-commᴹ tᴹ (uᴹ *ᴹ vᴹ))
          (*-assocᴹ uᴹ vᴹ tᴹ))
        (doubleCompPathP {B = Freeᴹ}
          (congP (λ _ → _*ᴹ vᴹ) (*-commᴹ tᴹ uᴹ))
          (*-assocᴹ uᴹ tᴹ vᴹ)
          (congP (λ _ → uᴹ *ᴹ_) (*-commᴹ tᴹ vᴹ)))
        refl
        refl


module _ (M : MotiveDep A ℓ) where
  open MotiveDep M

  elim : ∀ t → Freeᴹ t
  elim (ι x) = ιᴹ x
  elim ⊤ = ⊤ᴹ
  elim (t * u) = elim t *ᴹ elim u
  elim (t ⇒ u) = elim t ⇒ᴹ elim u
  elim (*-identityˡ t i) = *-identityˡᴹ (elim t) i
  elim (*-identityʳ t i) = *-identityʳᴹ (elim t) i
  elim (*-comm t u i) = *-commᴹ (elim t) (elim u) i
  elim (*-assoc t u v i) = *-assocᴹ (elim t) (elim u) (elim v) i
  elim (⇒-identityˡ t i) = ⇒-identityˡᴹ (elim t) i
  elim (⇒-curry t u v i) = ⇒-curryᴹ (elim t) (elim u) (elim v) i
  elim (⇒-annihilʳ t i) = ⇒-annihilʳᴹ (elim t) i
  elim (⇒-distribˡ t u v i) = ⇒-distribˡᴹ (elim t) (elim u) (elim v) i
  elim (*-bigon t u i j) = *-bigonᴹ (elim t) (elim u) i j
  elim (*-triangle t u i j) = *-triangleᴹ (elim t) (elim u) i j
  elim (*-pentagon t u v w i j) =
    *-pentagonᴹ (elim t) (elim u) (elim v) (elim w) i j
  elim (*-hexagon t u v i j) = *-hexagonᴹ (elim t) (elim u) (elim v) i j
  elim (trunc t u p q P Q i j k) =
    isGroupoid→CubeP (λ i j k → Freeᴹ (trunc t u p q P Q i j k))
      (λ j k → elim (P j k))
      (λ j k → elim (Q j k))
      (λ i k → elim (p k))
      (λ i k → elim (q k))
      (λ i j → elim t)
      (λ i j → elim u)
      (isGroupoidFreeᴹ u)
      i j k


record MotiveDepSet (A : Type ℓ) ℓ′ : Type (ℓ-suc (ℓ-max ℓ ℓ′)) where
  no-eta-equality
  infixr 5 _⇒ᴹ_
  infixr 6 _*ᴹ_
  field
    Freeᴹ : Free A → Type ℓ′
    isSetFreeᴹ : ∀ t → isSet (Freeᴹ t)
    ιᴹ : ∀ x → Freeᴹ (ι x)
    ⊤ᴹ : Freeᴹ ⊤
    _*ᴹ_ : ∀ {t u} (tᴹ : Freeᴹ t) (uᴹ : Freeᴹ u) → Freeᴹ (t * u)
    _⇒ᴹ_ : ∀ {t u} (tᴹ : Freeᴹ t) (uᴹ : Freeᴹ u) → Freeᴹ (t ⇒ u)

    *-identityˡᴹ : ∀ {t} tᴹ →
      PathP (λ i → Freeᴹ (*-identityˡ t i)) (⊤ᴹ *ᴹ tᴹ) tᴹ
    *-identityʳᴹ : ∀ {t} tᴹ →
      PathP (λ i → Freeᴹ (*-identityʳ t i)) (tᴹ *ᴹ ⊤ᴹ) tᴹ
    *-commᴹ : ∀ {t u} tᴹ uᴹ →
      PathP (λ i → Freeᴹ (*-comm t u i)) (tᴹ *ᴹ uᴹ) (uᴹ *ᴹ tᴹ)
    *-assocᴹ : ∀ {t u v} tᴹ uᴹ vᴹ →
      PathP (λ i → Freeᴹ (*-assoc t u v i))
        ((tᴹ *ᴹ uᴹ) *ᴹ vᴹ)
        (tᴹ *ᴹ (uᴹ *ᴹ vᴹ))

    ⇒-identityˡᴹ : ∀ {t} tᴹ →
      PathP (λ i → Freeᴹ (⇒-identityˡ t i)) tᴹ (⊤ᴹ ⇒ᴹ tᴹ)
    ⇒-curryᴹ : ∀ {t u v} tᴹ uᴹ vᴹ →
      PathP (λ i → Freeᴹ (⇒-curry t u v i))
        (tᴹ ⇒ᴹ uᴹ ⇒ᴹ vᴹ)
        (tᴹ *ᴹ uᴹ ⇒ᴹ vᴹ)
    ⇒-annihilʳᴹ : ∀ {t} tᴹ →
      PathP (λ i → Freeᴹ (⇒-annihilʳ t i)) (tᴹ ⇒ᴹ ⊤ᴹ) ⊤ᴹ
    ⇒-distribˡᴹ : ∀ {t u v} tᴹ uᴹ vᴹ →
      PathP (λ i → Freeᴹ (⇒-distribˡ t u v i))
        (tᴹ ⇒ᴹ uᴹ *ᴹ vᴹ)
        ((tᴹ ⇒ᴹ uᴹ) *ᴹ (tᴹ ⇒ᴹ vᴹ))

  *-bigonᴹ : ∀ {t u} tᴹ uᴹ →
    SquareP (λ i j → Freeᴹ (*-bigon t u i j))
      (*-commᴹ tᴹ uᴹ)
      (symP (*-commᴹ uᴹ tᴹ))
      refl
      refl
  *-bigonᴹ {t} {u} _ _ =
    isSet→SquareP (λ i j → isSetFreeᴹ (*-bigon t u i j))
      _ _ _ _

  *-triangleᴹ : ∀ {t u} tᴹ uᴹ →
    SquareP (λ i j → Freeᴹ (*-triangle t u i j))
      (*-assocᴹ tᴹ ⊤ᴹ uᴹ)
      (congP (λ _ → _*ᴹ uᴹ) (*-identityʳᴹ tᴹ))
      refl
      (congP (λ _ → tᴹ *ᴹ_) (*-identityˡᴹ uᴹ))
  *-triangleᴹ {t} {u} _ _ =
    isSet→SquareP (λ i j → isSetFreeᴹ (*-triangle t u i j))
      _ _ _ _

  *-pentagonᴹ : ∀ {t u v w} tᴹ uᴹ vᴹ wᴹ →
    SquareP (λ i j → Freeᴹ (*-pentagon t u v w i j))
      (compPathP' {B = Freeᴹ}
        (*-assocᴹ (tᴹ *ᴹ uᴹ) vᴹ wᴹ)
        (*-assocᴹ tᴹ uᴹ (vᴹ *ᴹ wᴹ)))
      (doubleCompPathP {B = Freeᴹ}
        (congP (λ _ → _*ᴹ wᴹ) (*-assocᴹ tᴹ uᴹ vᴹ))
        (*-assocᴹ tᴹ (uᴹ *ᴹ vᴹ) wᴹ)
        (congP (λ _ → tᴹ *ᴹ_) (*-assocᴹ uᴹ vᴹ wᴹ)))
      refl
      refl
  *-pentagonᴹ {t} {u} {v} {w} _ _ _ _ =
    isSet→SquareP (λ i j → isSetFreeᴹ (*-pentagon t u v w i j))
      _ _ _ _

  *-hexagonᴹ : ∀ {t u v} tᴹ uᴹ vᴹ →
    SquareP (λ i j → Freeᴹ (*-hexagon t u v i j))
      (doubleCompPathP {B = Freeᴹ}
        (*-assocᴹ tᴹ uᴹ vᴹ)
        (*-commᴹ tᴹ (uᴹ *ᴹ vᴹ))
        (*-assocᴹ uᴹ vᴹ tᴹ))
      (doubleCompPathP {B = Freeᴹ}
        (congP (λ _ → _*ᴹ vᴹ) (*-commᴹ tᴹ uᴹ))
        (*-assocᴹ uᴹ tᴹ vᴹ)
        (congP (λ _ → uᴹ *ᴹ_) (*-commᴹ tᴹ vᴹ)))
      refl
      refl
  *-hexagonᴹ {t} {u} {v} _ _ _ =
    isSet→SquareP (λ i j → isSetFreeᴹ (*-hexagon t u v i j))
      _ _ _ _

  motiveDep : MotiveDep A ℓ′
  motiveDep = record
    { Freeᴹ = Freeᴹ
    ; isGroupoidFreeᴹ = λ t → isSet→isGroupoid (isSetFreeᴹ t)
    ; ιᴹ = ιᴹ
    ; ⊤ᴹ = ⊤ᴹ
    ; _*ᴹ_ = _*ᴹ_
    ; _⇒ᴹ_ = _⇒ᴹ_
    ; *-identityˡᴹ = *-identityˡᴹ
    ; *-identityʳᴹ = *-identityʳᴹ
    ; *-commᴹ = *-commᴹ
    ; *-assocᴹ = *-assocᴹ
    ; ⇒-identityˡᴹ = ⇒-identityˡᴹ
    ; ⇒-curryᴹ = ⇒-curryᴹ
    ; ⇒-annihilʳᴹ = ⇒-annihilʳᴹ
    ; ⇒-distribˡᴹ = ⇒-distribˡᴹ
    ; *-bigonᴹ = *-bigonᴹ
    ; *-triangleᴹ = *-triangleᴹ
    ; *-pentagonᴹ = *-pentagonᴹ
    ; *-hexagonᴹ = *-hexagonᴹ
    }


module _ (M : MotiveDepSet A ℓ) where
  open MotiveDepSet M

  elimSet : ∀ t → Freeᴹ t
  elimSet = elim motiveDep


record Motive (A : Type ℓ) ℓ′ : Type (ℓ-suc (ℓ-max ℓ ℓ′)) where
  no-eta-equality
  infixr 5 _⇒ᴹ_
  infixr 6 _*ᴹ_
  field
    Freeᴹ : Type ℓ′
    isGroupoidFreeᴹ : isGroupoid Freeᴹ
    ιᴹ : (x : A) → Freeᴹ
    ⊤ᴹ : Freeᴹ
    _*ᴹ_ : (tᴹ uᴹ : Freeᴹ) → Freeᴹ
    _⇒ᴹ_ : (tᴹ uᴹ : Freeᴹ) → Freeᴹ

    *-identityˡᴹ : ∀ tᴹ → ⊤ᴹ *ᴹ tᴹ ≡ tᴹ
    *-identityʳᴹ : ∀ tᴹ → tᴹ *ᴹ ⊤ᴹ ≡ tᴹ
    *-commᴹ : ∀ tᴹ uᴹ → tᴹ *ᴹ uᴹ ≡ uᴹ *ᴹ tᴹ
    *-assocᴹ : ∀ tᴹ uᴹ vᴹ → (tᴹ *ᴹ uᴹ) *ᴹ vᴹ ≡ tᴹ *ᴹ (uᴹ *ᴹ vᴹ)

    ⇒-identityˡᴹ : ∀ tᴹ → tᴹ ≡ ⊤ᴹ ⇒ᴹ tᴹ
    ⇒-curryᴹ : ∀ tᴹ uᴹ vᴹ → tᴹ ⇒ᴹ uᴹ ⇒ᴹ vᴹ ≡ tᴹ *ᴹ uᴹ ⇒ᴹ vᴹ
    ⇒-annihilʳᴹ : ∀ tᴹ → tᴹ ⇒ᴹ ⊤ᴹ ≡ ⊤ᴹ
    ⇒-distribˡᴹ : ∀ tᴹ uᴹ vᴹ → tᴹ ⇒ᴹ uᴹ *ᴹ vᴹ ≡ (tᴹ ⇒ᴹ uᴹ) *ᴹ (tᴹ ⇒ᴹ vᴹ)

    *-bigonᴹ : ∀ tᴹ uᴹ → *-commᴹ tᴹ uᴹ ≡ sym (*-commᴹ uᴹ tᴹ)

    *-triangleᴹ : ∀ tᴹ uᴹ →
      Square
        (*-assocᴹ tᴹ ⊤ᴹ uᴹ)
        (cong (_*ᴹ uᴹ) (*-identityʳᴹ tᴹ))
        refl
        (cong (tᴹ *ᴹ_) (*-identityˡᴹ uᴹ))

    *-pentagonᴹ : ∀ tᴹ uᴹ vᴹ wᴹ →
      Path (((tᴹ *ᴹ uᴹ) *ᴹ vᴹ) *ᴹ wᴹ ≡ tᴹ *ᴹ (uᴹ *ᴹ (vᴹ *ᴹ wᴹ)))
        (*-assocᴹ (tᴹ *ᴹ uᴹ) vᴹ wᴹ ∙ *-assocᴹ tᴹ uᴹ (vᴹ *ᴹ wᴹ))
        (cong (_*ᴹ wᴹ) (*-assocᴹ tᴹ uᴹ vᴹ)
          ∙∙ *-assocᴹ tᴹ (uᴹ *ᴹ vᴹ) wᴹ
          ∙∙ cong (tᴹ *ᴹ_) (*-assocᴹ uᴹ vᴹ wᴹ))

    *-hexagonᴹ : ∀ tᴹ uᴹ vᴹ →
      Path ((tᴹ *ᴹ uᴹ) *ᴹ vᴹ ≡ uᴹ *ᴹ (vᴹ *ᴹ tᴹ))
        (*-assocᴹ tᴹ uᴹ vᴹ
          ∙∙ *-commᴹ tᴹ (uᴹ *ᴹ vᴹ)
          ∙∙ *-assocᴹ uᴹ vᴹ tᴹ)
        (cong (_*ᴹ vᴹ) (*-commᴹ tᴹ uᴹ)
          ∙∙ *-assocᴹ uᴹ tᴹ vᴹ
          ∙∙ cong (uᴹ *ᴹ_) (*-commᴹ tᴹ vᴹ))


module _ (M : Motive A ℓ) where
  open Motive M

  rec : Free A → Freeᴹ
  rec (ι x) = ιᴹ x
  rec ⊤ = ⊤ᴹ
  rec (t * u) = rec t *ᴹ rec u
  rec (t ⇒ u) = rec t ⇒ᴹ rec u
  rec (*-identityˡ t i) = *-identityˡᴹ (rec t) i
  rec (*-identityʳ t i) = *-identityʳᴹ (rec t) i
  rec (*-comm t u i) = *-commᴹ (rec t) (rec u) i
  rec (*-assoc t u v i) = *-assocᴹ (rec t) (rec u) (rec v) i
  rec (⇒-identityˡ t i) = ⇒-identityˡᴹ (rec t) i
  rec (⇒-curry t u v i) = ⇒-curryᴹ (rec t) (rec u) (rec v) i
  rec (⇒-annihilʳ t i) = ⇒-annihilʳᴹ (rec t) i
  rec (⇒-distribˡ t u v i) = ⇒-distribˡᴹ (rec t) (rec u) (rec v) i
  rec (*-bigon t u i j) = *-bigonᴹ (rec t) (rec u) i j
  rec (*-triangle t u i j) = *-triangleᴹ (rec t) (rec u) i j
  rec (*-pentagon t u v w i j) =
    (compPathP'≡compPath _ _
      ∙∙ *-pentagonᴹ (rec t) (rec u) (rec v) (rec w)
      ∙∙ sym (doubleCompPathP≡doubleCompPath _ _ _))
    i j
  rec (*-hexagon t u v i j) =
    (doubleCompPathP≡doubleCompPath _ _ _
      ∙∙ *-hexagonᴹ (rec t) (rec u) (rec v)
      ∙∙ sym (doubleCompPathP≡doubleCompPath _ _ _))
    i j
  rec (trunc t u p q P Q i j k) =
    isGroupoidFreeᴹ
      (rec t) (rec u)
      (λ i → rec (p i)) (λ i → rec (q i))
      (λ i j → rec (P i j)) (λ i j → rec (Q i j))
      i j k

--------------------------------------------------------------------------------

symmetricMonoidalGroupoid : (A : Type ℓ) → SymmetricMonoidalGroupoid ℓ
symmetricMonoidalGroupoid A = record
  { Carrier = Free A
  ; isGroupoidCarrier = trunc
  ; ⊤ = ⊤
  ; _*_ = _*_
  ; *-identityˡ = *-identityˡ
  ; *-identityʳ = *-identityʳ
  ; *-comm = *-comm
  ; *-assoc = *-assoc
  ; *-bigon = *-bigon
  ; *-triangle = *-triangle
  ; *-pentagon = *-pentagon
  ; *-hexagon = *-hexagon
  }
