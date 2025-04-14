open import foundations.Universes
open import foundations.Identity


module foundations.PathReasoning where


import foundations.Reasoning as FR
infixr 20 _⟩∙⟨_

module ∙ {𝓤} (A : Type 𝓤) = FR A _＝_ refl (λ x y → y ∙ x) ∙-reflr ∙-refll (λ r q p → ∙-assoc p q r)

_⟩∙⟨_ : ∀ {𝓤} {A : Type 𝓤} {x y z : A} {p q : x ＝ y} {r s : y ＝ z} → p ＝ q → r ＝ s → p ∙ r ＝ q ∙ s
p ⟩∙⟨ q = ∙._⟩⊙⟨_ _ q p

