open import Relation.Binary.PropositionalEquality as Eq using (_≡_; module ≡-Reasoning)



module Language.SystemF where



record SystemF : Set₂ where  
  field
    -- Sorts
    Type : Set₁

    -- The set of Agda values underlying a given System F type
    V : Type → Set

    -- Types
    _⇒_ : Type → Type → Type
    ∀' : (Type → Type) → Type

    -- Introductions
    ƛ : {A B : Type} → (V A → V B) → V (A ⇒ B)
    Λ : {tf : Type → Type} → ((A : Type) → V (tf A)) → V (∀' tf)
    
    -- Eliminations
    ap : {A B : Type} → V (A ⇒ B) → V A → V B
    tpap : {tf : Type → Type} → V (∀' tf) → (A : Type) → V (tf A)

  infixr 20 _⇒_

  infix 5 ƛ
  syntax ƛ (λ x → e) = ƛ x , e

  infix 5 ∀'
  syntax ∀' (λ α → A) = ∀' α , A

  infix 5 Λ
  syntax Λ (λ α → e) = Λ α , e

  field
    -- β-laws
    →-β : {A B : Type} {f : V A → V B} {e : V A} → ap (ƛ f) e ≡ f e
    ∀-β : {tf : Type → Type} {f : (α : Type) → V (tf α)} {A : Type} → tpap (Λ f) A ≡ f A

    -- η-laws
    →-η : {A B : Type} {e : V (A ⇒ B)} → ƛ (ap e) ≡ e
    ∀-η : {tf : Type → Type} {e : V (∀' tf)} → Λ (tpap e) ≡ e
  