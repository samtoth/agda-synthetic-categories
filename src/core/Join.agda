module core.Join where

open import foundations.Prelude
open import ufAxioms
open import ergonomics.Universal

_*_ : ∀ {𝓤 𝓥} → Type 𝓤 → Type 𝓥 → Type (𝓤 ⊔ 𝓥)
A * B = Pushout {A = A × B} fst snd



