module Foundations.IdentityEquiv where

open import Foundations.Universes
open import Foundations.Identity
open import Foundations.QuasiIsomorphism
open import Foundations.CoherentIsomorphism
open import Foundations.Homotopy
open import Foundations.Sigma
open import Foundations.Functions
open import Foundations.DependentIdentity
open import Foundations.FibrewiseEquiv
open import Foundations.Embedding
open import Foundations.EquivHomotopy

sym-qinv : ∀ {𝓤} {A : Type 𝓤} {a b : A} → quasi-inv (sym {x = a} {b})
sym-qinv .fst = sym
sym-qinv .snd .fst refl = refl
sym-qinv .snd .snd refl = refl

sym-is-equiv : ∀ {𝓤} {A : Type 𝓤} {a b : A} → is-equiv (sym {x = a} {b})
sym-is-equiv .is-equiv.qinv = sym-qinv
sym-is-equiv .is-equiv.coherent refl = refl

sym≃ : ∀ {𝓤} {A : Type 𝓤} {a b : A} → (a ＝ b) ≃ (b ＝ a)
sym≃ = mk≃ sym sym-is-equiv

＝-equiv : ∀ {𝓤 𝓥} {A : Type 𝓤} {B : Type 𝓥} → {a b : A}
          → (e : A ≃ B) → (a ＝ b) ≃ (e ._≃_.fwd a ＝ e ._≃_.fwd b)
＝-equiv (mk≃ fwd has-is-eqv) = mk≃ (ap fwd) (is-embedding←is-equiv has-is-eqv)

∙-is-equiv : ∀ {𝓤} {A : Type 𝓤} {a b c : A} (p : a ＝ b)
             → is-equiv (λ (q : b ＝ c) → p ∙ q)
∙-is-equiv refl = id-is-equiv

∙-is-equiv' : ∀ {𝓤} {A : Type 𝓤} {a b c : A} (p : b ＝ c)
             → is-equiv (λ (q : a ＝ b) → q ∙ p)
∙-is-equiv' refl = homotopy-is-equiv (λ where refl → refl) id-is-equiv

＝-postcomp-≃ : ∀ {𝓤} {A : Type 𝓤} {a b c : A} (p : a ＝ b)
               → (b ＝ c) ≃ (a ＝ c)
＝-postcomp-≃ p = mk≃ (λ q → p ∙ q) (∙-is-equiv p)

Idᶠ-const-≃
  : ∀ {𝓤 𝓥} {A : Type 𝓤} {B : Type 𝓥}
      (f : A → B)
      {x y : A} (p : x ＝ y)
      {l : B}
      (t : f x ＝ l)
      (r : f y ＝ l)
    → Idᶠ (λ z → f z ＝ l) p t r ≃ (ap f (sym p) ∙ t ＝ r)
Idᶠ-const-≃ f p t r = ＝-postcomp-≃ (sym (Idᵈ-const-coe f p t))

Idᶠ-const-≃'
  : ∀ {𝓤 𝓥} {A : Type 𝓤} {B : Type 𝓥}
      (f : A → B)
      {x y : A} (p : x ＝ y)
      {l : B}
      (t : l ＝ f x)
      (r : l ＝ f y)
    → Idᶠ (λ z → l ＝ f z) p t r ≃ (t ∙ ap f p ＝ r)
Idᶠ-const-≃' f refl t r = ＝-postcomp-≃ (∙-reflr t)

tr-is-equiv : ∀ {𝓤 𝓥} {A : Type 𝓤} {B : A → Type 𝓥}
                {a b : A} (p : a ＝ b)
              → is-equiv (tr B p)
tr-is-equiv {B = B} p = coe-is-equiv (ap B p)

fibre'≃fibre
  : ∀ {𝓤 𝓥} {A : Type 𝓤} {B : Type 𝓥}
      (f : A → B) (b : B)
  → fibre' f b ≃ fibre f b
fibre'≃fibre f b = Σ-ap-≃ λ _ → sym≃
