module ergonomics.auto where

open import foundations.Prelude 

auto! : ∀ {𝓤} {A : Type 𝓤} → ⦃ _ : A ⦄ → A
auto! ⦃ x ⦄ = x
