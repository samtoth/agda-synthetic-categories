module foundations.Empty where

open import foundations.universe

data ⊥ : Type where


¡_ : ∀ {𝓤} {A : Type 𝓤} → ⊥ → A
¡ ()

¬_ : ∀ {𝓤} → Type 𝓤 → Type 𝓤
¬ A = A → ⊥
