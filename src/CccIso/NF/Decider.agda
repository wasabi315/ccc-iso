module CccIso.NF.Decider where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function using (_∘_)
open import Cubical.Foundations.HLevels using
  (hProp; isSetHProp; isPropΠ; isProp→; isSetΠ2; isSetΠ)
open import Cubical.Foundations.Univalence using (hPropExt)
open import Cubical.Data.Empty using (⊥; isProp⊥)
open import Cubical.Data.Fin.Recursive using (Fin; discreteFin)
open import Cubical.Data.Nat.Base using (ℕ)
open import Cubical.Data.Sigma using (Σ-syntax; ∃-syntax; _,_)
open import Cubical.Data.Unit using (Unit; tt; isPropUnit)
open import Cubical.HITs.PropositionalTruncation as PT using (∥_∥₁; ∣_∣₁; squash₁)
open import Cubical.Relation.Nullary using
  (¬_; Dec; yes; no; isPropDec; decRec; mapDec)

open import CccIso.NF
open import CccIso.NF.Properties
open import CccIso.NF.SetTruncation

open ModelDepProp

private
  variable
    n : ℕ

--------------------------------------------------------------------------------

∥⊥∥→⊥ : ∥ ⊥ ∥₁ → ⊥
∥⊥∥→⊥ = PT.rec isProp⊥ λ x → x

module DecidePathExists where

  ⊤-case : (α : NF n) → Dec ∥ ⊤ ≡ α ∥₁
  ⊤-case =
    elimPropNF
      (λ _ → isPropDec squash₁)
      (yes ∣ refl ∣₁)
      (λ _ _ → no (PT.rec isProp⊥ (φ*α≢⊤ ∘ sym)))

  ⇒-case : {α : NF n} (α≟_ : ∀ β → Dec ∥ α ≡ β ∥₁) (x : Fin n) (φ : Factor n)
    → Dec ∥ α ⇒ι x ≡ φ ∥₁
  ⇒-case α≟_ x (β ⇒ι y) with discreteFin x y | α≟ β
  ... | no x≢y  | _       = no (PT.rec isProp⊥ (x≢y ∘ cong codomain))
  ... | yes x≡y | no α≢β  = no (PT.rec isProp⊥ (α≢β ∘ ∣_∣₁ ∘ cong domain))
  ... | yes x≡y | yes α≡β = yes (PT.map (λ α≡β → cong₂ _⇒ι_ α≡β x≡y) α≡β)

  -- Find a factor in an NF that is equivalent to a given factor
  find : {φ : Factor n} (φ≟_ : ∀ ψ → Dec ∥ φ ≡ ψ ∥₁) →
    (α : NF n) → Dec ∥ (Σ[ β ∈ _ ] Σ[ γ ∈ _ ] β * φ *ᶠ γ ≡ α) ∥₁
  find {φ = φ} φ≟_ =
    elimPropNF
      (λ _ → isPropDec squash₁)
      case1
      (λ ψ ∃βφγ≟α → decRec case2 (case3 ∃βφγ≟α) (φ≟ ψ))
    where
      -- Case 1: The given NF is ⊤
      case1 : Dec ∥ Σ[ β ∈ _ ] Σ[ γ ∈ _ ] β * φ *ᶠ γ ≡ ⊤ ∥₁
      case1 =
        no
          (PT.rec isProp⊥ λ (β , γ , βφγ≡⊤) →
            subst (λ δ → ¬ δ ≡ ⊤) (shift φ β γ) φ*α≢⊤ βφγ≡⊤)

      -- Case 2: The head of the given NF is equivalent to φ
      case2 : ∀ {ψ α} → ∥ φ ≡ ψ ∥₁ →
        Dec ∥ Σ[ β ∈ _ ] Σ[ γ ∈ _ ] β * φ *ᶠ γ ≡ ψ *ᶠ α ∥₁
      case2 {α = α} φ≡ψ =
        yes (PT.map (λ φ≡ψ → ⊤ , α , cong (_*ᶠ α) φ≡ψ) φ≡ψ)

      lemma : ∀ {φ ψ α} →
        ¬ ∥ φ ≡ ψ ∥₁ →
        ¬ ∥ Σ[ β ∈ _ ] Σ[ γ ∈ _ ] β * φ *ᶠ γ ≡ α ∥₁ →
        ¬ ∥ Σ[ β ∈ _ ] Σ[ γ ∈ _ ] β * φ *ᶠ γ ≡ ψ *ᶠ α ∥₁
      lemma {φ} {ψ} {α} φ≢ψ ∄βφγ≡α =
        PT.rec isProp⊥ λ (β , γ , βφγ≡ψα) →
          PT.rec isProp⊥
            (λ (δ , p , q) → ∄βφγ≡α ∣ ⊤ , δ , q ∣₁)
            (different-head φ ψ (β * γ) α (φ≢ψ ∘ ∣_∣₁) ∣ shift φ β γ ∙ βφγ≡ψα ∣₁)

      -- Case 3: The head of the given NF is not equivalent to φ
      case3 : ∀ {ψ α} →
        Dec ∥ Σ[ β ∈ _ ] Σ[ γ ∈ _ ] β * φ *ᶠ γ ≡ α ∥₁ →
        ¬ ∥ φ ≡ ψ ∥₁ →
        Dec ∥ Σ[ β ∈ _ ] Σ[ γ ∈ _ ] β * φ *ᶠ γ ≡ ψ *ᶠ α ∥₁
      case3 {ψ = ψ} (yes ∃βφγ≡α) φ≢ψ =
        yes (PT.map (λ (β , γ , βφγ≡α) → ψ *ᶠ β , γ , cong (ψ *ᶠ_) βφγ≡α) ∃βφγ≡α)
      case3 {ψ = ψ} {α = α} (no ∄βφγ≡α) φ≢ψ =
        no (lemma φ≢ψ ∄βφγ≡α)

  *-case : {φ : Factor n} {α : NF n} →
    (φ≟_ : ∀ ψ → Dec ∥ φ ≡ ψ ∥₁) (α≟_ : ∀ β → Dec ∥ α ≡ β ∥₁) →
    (β : NF n) → Dec ∥ φ *ᶠ α ≡ β ∥₁
  *-case {φ = φ} {α = α} φ≟_ α≟_ β =
    decRec
      (PT.rec
        (isPropDec squash₁)
        (λ (γ , δ , γφδ≡β) →
          decRec (case1 γ δ γφδ≡β) (case2 γ δ γφδ≡β) (α≟ (γ * δ))))
      case3
      (find φ≟_ β)
    where
      case1 : ∀ γ δ → γ * φ *ᶠ δ ≡ β → ∥ α ≡ γ * δ ∥₁ → Dec ∥ φ *ᶠ α ≡ β ∥₁
      case1 γ δ γφδ≡β α≡γδ =
        yes (PT.map (λ α≡γδ → cong (φ *ᶠ_) α≡γδ ∙∙ shift φ γ δ ∙∙ γφδ≡β) α≡γδ)

      case2 : ∀ γ δ → γ * φ *ᶠ δ ≡ β → ¬ ∥ α ≡ γ * δ ∥₁ → Dec ∥ φ *ᶠ α ≡ β ∥₁
      case2 γ δ γφδ≡β α≢γδ =
        no
          (PT.rec isProp⊥ λ φα≡β →
            α≢γδ (drop-∷ _ _ _ ∣ φα≡β ∙∙ sym γφδ≡β ∙∙ sym (shift φ γ δ) ∣₁))

      case3 : ¬ ∥ Σ[ γ ∈ _ ] Σ[ δ ∈ _ ] γ * φ *ᶠ δ ≡ β ∥₁ → Dec ∥ φ *ᶠ α ≡ β ∥₁
      case3 ∄γφδ≡β = no (PT.rec isProp⊥ λ φα≡β → ∄γφδ≡β ∣ ⊤ , α , φα≡β ∣₁)

  M : ModelDepProp _ _
  M .Factorᴹ φ = ∀ ψ → Dec ∥ φ ≡ ψ ∥₁
  M .NFᴹ α = ∀ β → Dec ∥ α ≡ β ∥₁
  M .isPropNFᴹ α = isPropΠ λ β → isPropDec squash₁
  M ._⇒ιᴹ_ = ⇒-case
  M .⊤ᴹ = ⊤-case
  M ._*ᴹ_ = *-case

  -- Decide the *existence* of a path between given two NF
  -- ∥_≟_∥ : (α β : NF n) → Dec ∥ α ≡ β ∥₁
  open ElimProp M using () renaming (⟦_⟧ⁿ to ∥_≟_∥) public

open DecidePathExists using (∥_≟_∥) public

module Test where
  open import Cubical.Data.Fin.Recursive using (zero; suc)

  A B [A] : NF 3
  A = ι zero
  B = ι (suc zero)
  [A] = ι (suc (suc zero))

  ty1 ty2 ty3 : NF 3
  ty1 = (A ⇒ B ⇒ B) ⇒ B ⇒ [A] ⇒ B
  ty2 = (B * A ⇒ B) ⇒ [A] ⇒ B ⇒ B
  ty3 = (B * A ⇒ A) ⇒ [A] ⇒ B ⇒ B

  _ : ∥ ty1 ≟ ty2 ∥ ≡ yes _
  _ = refl

  _ : ∥ ty1 ≟ ty3 ∥ ≡ no _
  _ = refl
