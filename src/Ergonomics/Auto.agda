module Ergonomics.Auto where

open import Foundations.Prelude 

auto! : ∀ {𝓤} {A : Type 𝓤} → ⦃ _ : A ⦄ → A
auto! ⦃ x ⦄ = x
