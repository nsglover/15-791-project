open import Relation.Binary.PropositionalEquality as Eq using (_≡_; module ≡-Reasoning)

open import Language.SystemF+
open import Language.SystemM



module Compile.M-to-F+ (F+ : SystemF+) where
open SystemF+ F+



data PosTyOp (D : Set₁) : Set₁ where
  Const : D → PosTyOp D
  Var : PosTyOp D
  Sum : PosTyOp D → PosTyOp D → PosTyOp D
  Prod : PosTyOp D → PosTyOp D → PosTyOp D
  Pow : D → PosTyOp D → PosTyOp D

Compile : SystemM

SystemM.Type Compile = Type
SystemM.V Compile = V

SystemM.PosTyOp Compile = PosTyOp Type

SystemM.Const Compile = Const
SystemM.Var Compile = Var
SystemM.Sum Compile = Sum
SystemM.Prod Compile = Prod
SystemM.Pow Compile = Pow

SystemM.eval Compile (Const B) A = B
SystemM.eval Compile Var A = A
SystemM.eval Compile (Sum P Q) A = SystemM.eval Compile P A + SystemM.eval Compile Q A
SystemM.eval Compile (Prod P Q) A = SystemM.eval Compile P A × SystemM.eval Compile Q A
SystemM.eval Compile (Pow B P) A = B ⇒ SystemM.eval Compile P A

SystemM.map Compile {Const C} f e = e
SystemM.map Compile {Var} f e = f e
SystemM.map Compile {Sum P Q} f e = case e (λ x → 1· SystemM.map Compile {P} f x) (λ y → 2· SystemM.map Compile {Q} f y)
SystemM.map Compile {Prod P Q} f e = ⟨ SystemM.map Compile {P} f (e ·1) , SystemM.map Compile {Q} f (e ·2) ⟩
SystemM.map Compile {Pow C P} f e = ƛ x , SystemM.map Compile {P} f (ap e x)

SystemM.⊥ Compile = ⊥
SystemM.⊤ Compile = ⊤
SystemM._+_ Compile = _+_
SystemM._×_ Compile = _×_
SystemM._⇒_ Compile = _⇒_
SystemM.μ Compile P = ∀' α , (SystemM.eval Compile P α ⇒ α) ⇒ α
SystemM.ν Compile P = {!   !}

SystemM.* Compile = *
SystemM.1·_ Compile = 1·_
SystemM.2·_ Compile = 2·_
SystemM.⟨_,_⟩ Compile = ⟨_,_⟩
SystemM.ƛ Compile = ƛ
SystemM.fold Compile {P} c = Λ α , ƛ f , ap f (SystemM.map Compile {P} (λ x → ap (tpap x α) f) c)
SystemM.gen Compile = {!   !}

SystemM.absurd Compile = absurd
SystemM.case Compile = case
SystemM._·1 Compile = _·1
SystemM._·2 Compile = _·2
SystemM.ap Compile = ap
SystemM.rec Compile {A = A} f e = ap (tpap e A) (ƛ f)
SystemM.unfold Compile = {!   !}

SystemM.eval-const Compile = Eq.refl
SystemM.eval-var Compile = Eq.refl
SystemM.eval-sum Compile = Eq.refl
SystemM.eval-prod Compile = Eq.refl
SystemM.eval-pow Compile = Eq.refl

SystemM.map-const Compile = Eq.refl
SystemM.map-var Compile = Eq.refl
SystemM.map-sum Compile = Eq.refl
SystemM.map-prod Compile = Eq.refl
SystemM.map-pow Compile = Eq.refl

SystemM.+-β₁ Compile = +-β₁
SystemM.+-β₂ Compile = +-β₂
SystemM.×-β₁ Compile = ×-β₁
SystemM.×-β₂ Compile = ×-β₂
SystemM.→-β Compile = →-β
SystemM.μ-β Compile {P} {A} {f} {e} =
  let open ≡-Reasoning in
    begin
      ap (tpap (Λ α , ƛ f , ap f (SystemM.map Compile {P} (λ x → ap (tpap x α) f) e)) A) (ƛ f)
    ≡⟨ Eq.cong (λ s → ap s (ƛ f)) ∀-β ⟩
      ap (ƛ f , ap f (SystemM.map Compile {P} (λ x → ap (tpap x A) f) e)) (ƛ f)
    ≡⟨ →-β ⟩
      ap (ƛ f) (SystemM.map Compile {P} (λ x → ap (tpap x A) (ƛ f)) e)
    ≡⟨ →-β ⟩
      f (SystemM.map Compile {P} (λ x → ap (tpap x A) (ƛ f)) e)
    ∎
SystemM.ν-β Compile = {!   !}

SystemM.+-η Compile = +-η
SystemM.×-η Compile = ×-η
SystemM.→-η Compile = →-η
SystemM.μ-η Compile {P} {e} = {!   !}
SystemM.ν-η Compile = {!   !}
