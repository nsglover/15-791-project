open import Relation.Binary.PropositionalEquality as Eq using (_≡_; module ≡-Reasoning)

open import Axioms
open import Language.SystemF+
open import Language.SystemM



module Compile.M-to-F+ (F+ : SystemF+) where
open SystemF+ F+



data PosTyOp : Set₁ where
  Const : Type → PosTyOp
  Var : PosTyOp
  Sum : PosTyOp → PosTyOp → PosTyOp
  Prod : PosTyOp → PosTyOp → PosTyOp
  Pow : Type → PosTyOp → PosTyOp

eval : PosTyOp → Type → Type
eval (Const B) A = B
eval Var A = A
eval (Sum P Q) A = eval P A + eval Q A
eval (Prod P Q) A = eval P A × eval Q A
eval (Pow B P) A = B ⇒ eval P A

map : {A B : Type} → (P : PosTyOp) → (V A → V B) → V (eval P A) → V (eval P B)
map (Const C) f e = e
map Var f e = f e
map (Sum P Q) f e = case e (λ x → 1· map P f x) (λ y → 2· map Q f y)
map (Prod P Q) f e = ⟨ map P f (e ·1) , map Q f (e ·2) ⟩
map (Pow C P) f e = ƛ x , map P f (ap e x)



Compile : SystemM

SystemM.Type Compile = Type
SystemM.V Compile = V

SystemM.PosTyOp Compile = PosTyOp

SystemM.Const Compile = Const
SystemM.Var Compile = Var
SystemM.Sum Compile = Sum
SystemM.Prod Compile = Prod
SystemM.Pow Compile = Pow

SystemM.eval Compile = eval
SystemM.map Compile {P} = map P

SystemM.⊥ Compile = ⊥
SystemM.⊤ Compile = ⊤
SystemM._+_ Compile = _+_
SystemM._×_ Compile = _×_
SystemM._⇒_ Compile = _⇒_
SystemM.μ Compile P = ∀' α , (eval P α ⇒ α) ⇒ α
SystemM.ν Compile P = ∃ α , α × (α ⇒ eval P α)

SystemM.* Compile = *
SystemM.1·_ Compile = 1·_
SystemM.2·_ Compile = 2·_
SystemM.⟨_,_⟩ Compile = ⟨_,_⟩
SystemM.ƛ Compile = ƛ
SystemM.fold Compile {P} c = Λ α , ƛ f , ap f (map P (λ x → ap (tpap x α) f) c)
SystemM.gen Compile {A = A} f s = pack A ⟨ s , ƛ f ⟩

SystemM.absurd Compile = absurd
SystemM.case Compile = case
SystemM._·1 Compile = _·1
SystemM._·2 Compile = _·2
SystemM.ap Compile = ap
SystemM.rec Compile {A = A} f e = ap (tpap e A) (ƛ f)
SystemM.unfold Compile {P} e = unpack e (λ α p → map P (λ s → pack α ⟨ s , p ·2 ⟩) (ap (p ·2) (p ·1)))

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
      ap (tpap (Λ α , ƛ f , ap f (map P (λ x → ap (tpap x α) f) e)) A) (ƛ f)
    ≡⟨ Eq.cong (λ s → ap s (ƛ f)) ∀-β ⟩
      ap (ƛ f , ap f (map P (λ x → ap (tpap x A) f) e)) (ƛ f)
    ≡⟨ →-β ⟩
      ap (ƛ f) (map P (λ x → ap (tpap x A) (ƛ f)) e)
    ≡⟨ →-β ⟩
      f (map P (λ x → ap (tpap x A) (ƛ f)) e)
    ∎
SystemM.ν-β Compile {P} {A} {f} {e} =
  let open ≡-Reasoning in
    begin
      unpack (pack A ⟨ e , ƛ f ⟩) (λ α p → map P (λ s → pack α ⟨ s , p ·2 ⟩) (ap (p ·2) (p ·1)))
    ≡⟨ ∃-β ⟩
      map P (λ s → pack A ⟨ s , ⟨ e , ƛ f ⟩ ·2 ⟩) (ap (⟨ e , ƛ f ⟩ ·2) (⟨ e , ƛ f ⟩ ·1))
    ≡⟨ Eq.cong₂ (λ s₁ s₂ → map P (λ s → pack A ⟨ s , ⟨ e , ƛ f ⟩ ·2 ⟩) (ap s₁ s₂)) ×-β₂ ×-β₁ ⟩
      map P (λ s → pack A ⟨ s , ⟨ e , ƛ f ⟩ ·2 ⟩) (ap (ƛ f) e)
    ≡⟨ Eq.cong (map P _) →-β ⟩
      map P (λ s → pack A ⟨ s , ⟨ e , ƛ f ⟩ ·2 ⟩) (f e)
    ≡⟨ Eq.cong (λ s → map P s (f e)) (funext (λ x → Eq.cong (λ s → pack A ⟨ x , s ⟩) ×-β₂)) ⟩
      map P (λ s → pack A ⟨ s , ƛ f ⟩) (f e)
    ∎

SystemM.+-η Compile = +-η
SystemM.×-η Compile = ×-η
SystemM.→-η Compile = →-η
SystemM.μ-η Compile {P} {e} = {!   !}
SystemM.ν-η Compile {P} {e} = {!   !}
