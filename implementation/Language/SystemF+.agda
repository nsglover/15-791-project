open import Relation.Binary.PropositionalEquality as Eq using (_≡_; module ≡-Reasoning)



module Language.SystemF+ where



record SystemF+ : Set₂ where
  field
    -- Sorts
    Type : Set₁
  
    -- The set of Agda values underlying a given System F type
    V : Type → Set

    -- Types
    ⊥ : Type
    ⊤ : Type
    _+_ : Type → Type → Type
    _×_ : Type → Type → Type
    _⇒_ : Type → Type → Type
    ∀' : (Type → Type) → Type
    ∃ : (Type → Type) → Type

    -- Introductions
    * : V ⊤
    1·_ : {A B : Type} → V A → V (A + B)
    2·_ : {A B : Type} → V B → V (A + B)
    ⟨_,_⟩ : {A B : Type} → V A → V B → V (A × B)
    ƛ : {A B : Type} → (V A → V B) → V (A ⇒ B)
    Λ : {tf : Type → Type} → ((A : Type) → V (tf A)) → V (∀' tf)
    pack : {tf : Type → Type} → (A : Type) → V (tf A) → V (∃ tf)

    -- Eliminations
    absurd : {A : Type} → V ⊥ → V A
    case : {A B C : Type} → V (A + B) → (V A → V C) → (V B → V C) → V C
    _·1 : {A B : Type} → V (A × B) → V A
    _·2 : {A B : Type} → V (A × B) → V B
    ap : {A B : Type} → V (A ⇒ B) → V A → V B
    tpap : {tf : Type → Type} → V (∀' tf) → (A : Type) → V (tf A)
    unpack : {B : Type} {tf : Type → Type} → V (∃ tf) → ((A : Type) → V (tf A) → V B) → V B

  infix 5 ƛ
  syntax ƛ (λ x → e) = ƛ x , e

  infix 5 ∀'
  syntax ∀' (λ α → A) = ∀' α , A

  infix 5 Λ
  syntax Λ (λ α → e) = Λ α , e

  infix 5 ∃
  syntax ∃ (λ α → A) = ∃ α , A

  field
    -- β-laws
    +-β₁ : {A B C : Type} {fa : V A → V C} {fb : V B → V C} {e : V A} → case (1· e) fa fb ≡ fa e
    +-β₂ : {A B C : Type} {fa : V A → V C} {fb : V B → V C} {e : V B} → case (2· e) fa fb ≡ fb e
    ×-β₁ : {A B : Type} {e₁ : V A} {e₂ : V B} → ⟨ e₁ , e₂ ⟩ ·1 ≡ e₁
    ×-β₂ : {A B : Type} {e₁ : V A} {e₂ : V B} → ⟨ e₁ , e₂ ⟩ ·2 ≡ e₂
    →-β : {A B : Type} {f : V A → V B} {e : V A} → ap (ƛ f) e ≡ f e
    ∀-β : {tf : Type → Type} {f : (α : Type) → V (tf α)} {A : Type} → tpap (Λ f) A ≡ f A
    ∃-β : {A C : Type} {tf : Type → Type} {e : V (tf A)} {f : (B : Type) → V (tf B) → V C} → unpack (pack A e) f ≡ f A e

    -- η-laws
    +-η : {A B C : Type} {e : V (A + B)} {f : V (A + B) → V C} → case e (λ x → f (1· x)) (λ y → f (2· y)) ≡ f e
    ×-η : {A B : Type} {e : V (A × B)} → ⟨ e ·1 , e ·2 ⟩ ≡ e
    →-η : {A B : Type} {e : V (A ⇒ B)} → ƛ (ap e) ≡ e
    ∀-η : {tf : Type → Type} {e : V (∀' tf)} → Λ (tpap e) ≡ e
    ∃-η : {tf : Type → Type} {e : V (∃ tf)} → unpack e (λ α x → pack α x) ≡ e
