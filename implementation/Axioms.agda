open import Relation.Binary.PropositionalEquality as Eq using (_≡_; module ≡-Reasoning)

postulate
  funext : {A B : Set} {f g : A → B} → ((a : A) → f a ≡ g a) → f ≡ g