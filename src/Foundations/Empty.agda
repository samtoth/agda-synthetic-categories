module Foundations.Empty where

open import Foundations.Universes

data ∅ : Type where


¡_ : ∀ {𝓤} {A : Type 𝓤} → ∅ → A
¡ ()

¬_ : ∀ {𝓤} → Type 𝓤 → Type 𝓤
¬ A = A → ∅
