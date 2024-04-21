open import Relation.Binary.PropositionalEquality as Eq using (_≡_; module ≡-Reasoning)



module Language.SystemM where



record SystemM : Set₂ where
  field
    -- Sorts
    Type : Set₁
  
    -- The set of Agda values underlying a given System F type
    V : Type → Set

    -- Positive Type Operators
    PosTyOp : Set₁
    Const : Type → PosTyOp
    Var : PosTyOp
    Sum : PosTyOp → PosTyOp → PosTyOp
    Prod : PosTyOp → PosTyOp → PosTyOp
    Pow : Type → PosTyOp → PosTyOp

    -- Operations on Positive Type Operators
    eval : PosTyOp → Type → Type
    map : {P : PosTyOp} {A B : Type} → (V A → V B) → V (eval P A) → V (eval P B)

    -- Types
    ⊥ : Type
    ⊤ : Type
    _+_ : Type → Type → Type
    _×_ : Type → Type → Type
    _⇒_ : Type → Type → Type
    μ : PosTyOp → Type
    ν : PosTyOp → Type

    -- Introductions
    * : V ⊤
    1·_ : {A B : Type} → V A → V (A + B)
    2·_ : {A B : Type} → V B → V (A + B)
    ⟨_,_⟩ : {A B : Type} → V A → V B → V (A × B)
    ƛ : {A B : Type} → (V A → V B) → V (A ⇒ B)
    fold : {P : PosTyOp} → V (eval P (μ P)) → V (μ P)
    gen : {P : PosTyOp} {A : Type} → (V A → V (eval P A)) → V A → V (ν P)

    -- Eliminations
    absurd : {A : Type} → V ⊥ → V A
    case : {A B C : Type} → V (A + B) → (V A → V C) → (V B → V C) → V C
    _·1 : {A B : Type} → V (A × B) → V A
    _·2 : {A B : Type} → V (A × B) → V B
    ap : {A B : Type} → V (A ⇒ B) → V A → V B
    rec : {P : PosTyOp} {A : Type} → (V (eval P A) → V A) → V (μ P) → V A
    unfold : {P : PosTyOp} → V (ν P) → V (eval P (ν P))

  infix 5 ƛ
  syntax ƛ (λ x → e) = ƛ x , e

  field
    -- eval laws
    eval-const : {A B : Type} → eval (Const B) A ≡ B
    eval-var : {A : Type} → eval Var A ≡ A
    eval-sum : {P Q : PosTyOp} {A : Type} → eval (Sum P Q) A ≡ eval P A + eval Q A
    eval-prod : {P Q : PosTyOp} {A : Type} → eval (Prod P Q) A ≡ eval P A × eval Q A
    eval-pow : {P : PosTyOp} {A B : Type} → eval (Pow B P) A ≡ B ⇒ eval P A

    -- map laws
    map-const : {A B C : Type} {f : V A → V B} {e : V C} → 
      map f (Eq.subst V (Eq.sym eval-const) e) ≡ Eq.subst V (Eq.sym eval-const) e
    map-var : {A B : Type} {f : V A → V B} {e : V A} →
      map f (Eq.subst V (Eq.sym eval-var) e) ≡ Eq.subst V (Eq.sym eval-var) (f e)
    map-sum : {P Q : PosTyOp} {A B : Type} {f : V A → V B} {e : V (eval P A + eval Q A)} →
      map f (Eq.subst V (Eq.sym eval-sum) e) ≡ 
      Eq.subst V (Eq.sym eval-sum) (case e (λ x → 1· map f x) (λ y → 2· map f y))
    map-prod : {P Q : PosTyOp} {A B : Type} {f : V A → V B} {e : V (eval P A × eval Q A)} →
      map f (Eq.subst V (Eq.sym eval-prod) e) ≡ 
      Eq.subst V (Eq.sym eval-prod) ⟨ map f (e ·1) , map f (e ·2) ⟩
    map-pow : {P : PosTyOp} {A B C : Type} {f : V A → V B} {e : V (C ⇒ eval P A)} →
      map f (Eq.subst V (Eq.sym eval-pow) e) ≡ Eq.subst V (Eq.sym eval-pow) (ƛ x , map f (ap e x))

    -- β-laws
    +-β₁ : {A B C : Type} {fa : V A → V C} {fb : V B → V C} {e : V A} → case (1· e) fa fb ≡ fa e
    +-β₂ : {A B C : Type} {fa : V A → V C} {fb : V B → V C} {e : V B} → case (2· e) fa fb ≡ fb e
    ×-β₁ : {A B : Type} {e₁ : V A} {e₂ : V B} → ⟨ e₁ , e₂ ⟩ ·1 ≡ e₁
    ×-β₂ : {A B : Type} {e₁ : V A} {e₂ : V B} → ⟨ e₁ , e₂ ⟩ ·2 ≡ e₂
    →-β : {A B : Type} {f : V A → V B} {e : V A} → ap (ƛ f) e ≡ f e
    μ-β : {P : PosTyOp} {A : Type} {f : V (eval P A) → V A} {e : V (eval P (μ P))} → rec f (fold e) ≡ f (map (rec f) e)
    ν-β : {P : PosTyOp} {A : Type} {f : V A → V (eval P A)} {e : V A} → unfold (gen f e) ≡ map (gen f) (f e)

    -- η-laws
    +-η : {A B C : Type} {e : V (A + B)} {f : V (A + B) → V C} → case e (λ x → f (1· x)) (λ y → f (2· y)) ≡ f e
    ×-η : {A B : Type} {e : V (A × B)} → ⟨ e ·1 , e ·2 ⟩ ≡ e
    →-η : {A B : Type} {e : V (A ⇒ B)} → ƛ (ap e) ≡ e
    μ-η : {P : PosTyOp} {e : V (μ P)} → rec fold e ≡ e
    ν-η : {P : PosTyOp} {e : V (ν P)} → gen unfold e ≡ e
 