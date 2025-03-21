module foundations.DependentHomotopy where

open import foundations.universe
open import foundations.Identity
open import foundations.DependentIdentity
open import foundations.Functions
open import foundations.Homotopy


HomotopyP : ∀ {𝓤 𝓥 𝓦} {A : Type 𝓤}
              → {B : Type 𝓥}
              → (C : A → B → Type 𝓦)
              → {x : B} 
              → (f : ∀ a → C a x)
              → {y : B} → (p : x ＝ y)
              → (g : ∀ a → C a y)
              → Type _
HomotopyP {A = A} {B} C f p g = ∀ (a : A) → IdP {A = B} (λ b → C a b) (f a) p (g a)

_~[_]_ : ∀ {𝓤 𝓥 𝓦} {A : Type 𝓤}
              → {B : Type 𝓥}
              → {C : A → B → Type 𝓦}
              → {x : A} 
              → (f : ∀ b → C x b)
              → {y : A} → (p : x ＝ y)
              → (g : ∀ b → C y b)
              → Type _
f ~[ p ] g = HomotopyP _ f p g               

infix 10 _~[_]_
{-# DISPLAY HomotopyP _ f p g = f ~[ p ] g #-}

module _ {𝓤 𝓥} {A : Type 𝓤} {B : Type 𝓥}  where
  happlyᵈ : ∀ {𝓦} {C : (a : A) → B → Type 𝓦}
            {x y : A} (p : x ＝ y)
            {f : (b : B) → C x b}
          → {g : (b : B) → C y b}
          → f ＝[ p ] g
          → f ~[ p ] g
  happlyᵈ refl refl b = refl
