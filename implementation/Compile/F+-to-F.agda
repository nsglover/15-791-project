open import Relation.Binary.PropositionalEquality as Eq using (_≡_; module ≡-Reasoning)

open import Language.SystemF
open import Language.SystemF+



module Compile.F+-to-F (F : SystemF) where
open SystemF F



Compile : SystemF+

SystemF+.Type Compile = Type
SystemF+.V Compile = V

SystemF+.⊥ Compile = ∀' α , α
SystemF+.⊤ Compile = ∀' α , α ⇒ α
SystemF+._+_ Compile A B = ∀' α , (A ⇒ α) ⇒ (B ⇒ α) ⇒ α
SystemF+._×_ Compile A B = ∀' α , (A ⇒ B ⇒ α) ⇒ α
SystemF+._⇒_ Compile = _⇒_
SystemF+.∀' Compile = ∀'

SystemF+.* Compile = Λ α , ƛ x , x
SystemF+.1·_ Compile e = Λ α , ƛ fa , ƛ fb , ap fa e
SystemF+.2·_ Compile e = Λ α , ƛ fa , ƛ fb , ap fb e
SystemF+.⟨_,_⟩ Compile e₁ e₂ = Λ α , ƛ fab , ap (ap fab e₁) e₂
SystemF+.ƛ Compile = ƛ
SystemF+.Λ Compile = Λ

SystemF+.absurd Compile {A = A} e = tpap e A
SystemF+.case Compile {C = C} e fa fb = ap (ap (tpap e C) (ƛ fa)) (ƛ fb)
SystemF+._·1 Compile {A = A} e = ap (tpap e A) (ƛ x , ƛ y , x)
SystemF+._·2 Compile {B = B} e = ap (tpap e B) (ƛ x , ƛ y , y)
SystemF+.ap Compile = ap
SystemF+.tpap Compile = tpap

SystemF+.+-β₁ Compile {A} {B} {C} {fa} {fb} {e} =
  let open ≡-Reasoning in
    begin
      ap (ap (tpap (Λ α , ƛ fa , ƛ fb , ap fa e) C) (ƛ fa)) (ƛ fb)
    ≡⟨ Eq.cong (λ s → ap (ap s (ƛ fa)) (ƛ fb)) ∀-β ⟩
      ap (ap (ƛ fa , ƛ fb , ap fa e) (ƛ fa)) (ƛ fb)
    ≡⟨ Eq.cong (λ s → ap s (ƛ fb)) →-β ⟩
     ap (ƛ fb , ap (ƛ fa) e) (ƛ fb)
    ≡⟨ →-β ⟩
     ap (ƛ fa) e
    ≡⟨ →-β ⟩
      fa e
    ∎
SystemF+.+-β₂ Compile {A} {B} {C} {fa} {fb} {e} =
  let open ≡-Reasoning in
    begin
      ap (ap (tpap (Λ α , ƛ fa , ƛ fb , ap fb e) C) (ƛ fa)) (ƛ fb)
    ≡⟨ Eq.cong (λ s → ap (ap s (ƛ fa)) (ƛ fb)) ∀-β ⟩
      ap (ap (ƛ fa , ƛ fb , ap fb e) (ƛ fa)) (ƛ fb)
    ≡⟨ Eq.cong (λ s → ap s (ƛ fb)) →-β ⟩
     ap (ƛ fb , ap fb e) (ƛ fb)
    ≡⟨ →-β ⟩
     ap (ƛ fb) e
    ≡⟨ →-β ⟩
      fb e
    ∎
SystemF+.×-β₁ Compile {A} {B} {e₁} {e₂} =
  let open ≡-Reasoning in
    begin
      ap (tpap (Λ α , ƛ fab , ap (ap fab e₁) e₂) A) (ƛ x , ƛ y , x)
    ≡⟨ Eq.cong (λ s → ap s (ƛ x , ƛ y , x)) ∀-β ⟩
      ap (ƛ fab , ap (ap fab e₁) e₂) (ƛ x , ƛ y , x)
    ≡⟨ →-β ⟩
      ap (ap (ƛ x , ƛ y , x) e₁) e₂
    ≡⟨ Eq.cong (λ s → ap s e₂) →-β ⟩
      ap (ƛ y , e₁) e₂
    ≡⟨ →-β ⟩
      e₁
    ∎
SystemF+.×-β₂ Compile {A} {B} {e₁} {e₂} =
  let open ≡-Reasoning in
    begin
      ap (tpap (Λ α , ƛ fab , ap (ap fab e₁) e₂) B) (ƛ x , ƛ y , y)
    ≡⟨ Eq.cong (λ s → ap s (ƛ x , ƛ y , y)) ∀-β ⟩
      ap (ƛ fab , ap (ap fab e₁) e₂) (ƛ x , ƛ y , y)
    ≡⟨ →-β ⟩
      ap (ap (ƛ x , ƛ y , y) e₁) e₂
    ≡⟨ Eq.cong (λ s → ap s e₂) →-β ⟩
      ap (ƛ y , y) e₂
    ≡⟨ →-β ⟩
      e₂
    ∎
SystemF+.→-β Compile = →-β
SystemF+.∀-β Compile = ∀-β

SystemF+.+-η Compile = {!   !}
SystemF+.×-η Compile = {!   !}
SystemF+.→-η Compile = →-η
SystemF+.∀-η Compile = ∀-η
