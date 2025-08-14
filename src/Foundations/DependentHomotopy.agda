module Foundations.DependentHomotopy where

open import Foundations.Universes
open import Foundations.Identity
open import Foundations.DependentIdentity
open import Foundations.Functions
open import Foundations.Homotopy


HomotopyP : ∀ {𝓤 𝓥} {A : Type 𝓤}
              → {B : A → Type 𝓥}
              → {C : A → Type 𝓥}
              → (P : B ~ C)
              → (f : ∀ a → B a)
              → (g : ∀ a → C a)
              → Type _
HomotopyP {A = A} P f g = ∀ (a : A) → IdP (P a) (f a) (g a)

HomotopyP-syntax : ∀ {𝓤 𝓥} {A : Type 𝓤}
              → {B : A → Type 𝓥}
              → {C : A → Type 𝓥}
              → (P : B ~ C)
              → (f : ∀ a → B a)
              → (g : ∀ a → C a)
              → Type _
HomotopyP-syntax = HomotopyP

syntax HomotopyP-syntax P f g = f ~[ P ] g

{-# DISPLAY HomotopyP P f g = f ~[ P ] g #-}

HomotopyP-const : ∀ {𝓤 𝓥} {A : Type 𝓤}
                    {B : A → Type 𝓥}
                    {f g : Π A B}
                    {p : B ~ B}
                    (_ : p ＝ ~refl)
                    → f ~ g → f ~[ p ] g
HomotopyP-const {f = f} {g} refl h = h


-- HomotopyP-sq : ∀ {𝓤 𝓥} {A : Type 𝓤}
--                  {B : A → Type 𝓥}
--                  {C : A → Type 𝓥}
--                  {f : Π A B}
--                  {g : Π A C}
--                  {p : B ~ C}
--                  → ~refl {f = f} ~[ {!!} ] ~refl {f = g}
-- HomotopyP-sq = {!!}                 

module _ {𝓤 𝓥} {A : Type 𝓤} {B C : A → Type 𝓥}   where
  happlyᵈ : ∀ {P : B ＝ C}
          → {f : ∀ a → B a}
          → {g : ∀ a → C a}
          → f ＝[ ap (λ f → (a : A) → f a) P ] g
          → f ~[ happly P ] g
  happlyᵈ {P = refl} p = happly p



_◂ᵈ_ : ∀ {𝓤 𝓥 𝓦} {A : Type 𝓤} {B : A → Type 𝓥} {C : ∀ {a} → B a → Type 𝓦}
         {f g : (a : A) → B a}
         (x : ∀ {a} → (b : B a) → C b)
         (h : f ~ g)
       → (x ∘ f) ~[ C ◂ h ] (x ∘ g)
_◂ᵈ_ {A = A} {B} {C} x h a = apᵈ x (h a)
