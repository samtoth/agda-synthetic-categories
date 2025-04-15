module ergonomics.Marker where

open import foundations.Prelude

⌜_⌝ : ∀ {𝓤} {A : Type 𝓤} → A → A
⌜ x ⌝ = x
{-# NOINLINE ⌜_⌝ #-}
