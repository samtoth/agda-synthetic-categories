module axioms.FunExt where

open import foundations.Prelude
open import foundations.FunExt


postulate
  weak-funext : ∀ {𝓤 𝓥} {A : Type 𝓤} {B : A → Type 𝓥}
                → (∀ a → is-singleton (B a))
                → is-singleton ((a : A) → B a)

  global-funext : FunExtGlobal


private module fe {𝓤} {𝓥} = WithFunExt {𝓤} {𝓥} global-funext
open fe public

open import foundations.EquivSingleton global-funext public 

funext-redex : ∀ {𝓤 𝓥} {A : Type 𝓤} {B : A → Type 𝓥}
               { f g : (a : A) → B a } → {p : f ~ g}
               → happly (funext→ p) ＝ p
funext-redex {p = p} = is-equiv.ε global-funext p

{-# REWRITE funext-redex #-}
