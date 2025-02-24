open import foundations.universe
open import foundations.Homotopy
open import foundations.Identity

module foundations.HomotopyReasoning where

import foundations.Reasoning as FR

module ~ {𝓤 𝓥} {A : Type 𝓤} {B : A → Type 𝓥} = FR ((a : A) → B a) _~_ ~refl (λ a b → b ~∙ a) {!!}
