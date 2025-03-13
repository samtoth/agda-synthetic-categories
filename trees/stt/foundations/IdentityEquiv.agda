module foundations.IdentityEquiv where

open import foundations.universe
open import foundations.Identity
open import foundations.QuasiIsomorphism
open import foundations.CoherentIsomorphism
open import foundations.Sigma

sym-qiso : ∀ {𝓤} {A : Type 𝓤} {a b : A} → quasi-iso (sym {x = a} {b})
sym-qiso .fst = sym
sym-qiso .snd .fst refl = refl
sym-qiso .snd .snd refl = refl

sym-is-equiv : ∀ {𝓤} {A : Type 𝓤} {a b : A} → is-equiv (sym {x = a} {b})
sym-is-equiv = is-equiv←qiso sym-qiso

sym≃ : ∀ {𝓤} {A : Type 𝓤} {a b : A} → (a ＝ b) ≃ (b ＝ a)
sym≃ = sym , sym-is-equiv
