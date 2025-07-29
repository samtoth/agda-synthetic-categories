module Foundations.Extension where


open import Foundations.Universes
open import Foundations.Identity
open import Foundations.Functions


record Ext {𝓤 𝓥 𝓦} {A : Type 𝓤} {B : Type 𝓥}
           (f : A → B) (C : B → Type 𝓦) (over : (a : A) → C (f a))  : Type (𝓤 ⊔ 𝓥 ⊔ 𝓦) where
  constructor mk-ext
  field
    at : Π B C
    agree : ∀ {a} → at (f a) ＝ over a


pattern ƛ f = mk-ext f refl
