module ergonomics.Core where

open import foundations.Prelude
open import ergonomics.Universal public
open import ergonomics.Extensionality public

auto! : ∀ {𝓤} {A : Type 𝓤} → ⦃ _ : A ⦄ → A
auto! ⦃ a ⦄ = a

