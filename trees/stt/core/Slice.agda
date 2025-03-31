module foundations.Slice where

-- Although we don't have the tools to talk about it
-- in full generality yet, if we fix a type A, we
-- can consider the large slice ∞-category 𝓢ω/A

open import foundations.universe
open import foundations.Sigma
open import foundations.Functions
open import foundations.Homotopy
open import foundations.Identity

Slice-map : ∀ {𝓤} {A : Type 𝓤}
              {𝓥} {B : Type 𝓥} (p : B → A) {𝓦}
              {C : Type 𝓦} (q : C → A)
              → Type (𝓤 ⊔ 𝓥 ⊔ 𝓦)
Slice-map {B = B} p {C = C} q = Σ[ f ∶ (B → C) ] (q ∘ f ~ p)

    
slice-fibre : ∀ {𝓤} {A : Type 𝓤}
              {𝓥} {B : Type 𝓥} (p : B → A) {𝓦}
              {C : Type 𝓦} (q : C → A)
              (a : A) →
              Slice-map p q →
              (fibre p a → fibre q a)
slice-fibre p q a (f , comm) (b , fib) = (f b , comm b ∙ fib)
 
