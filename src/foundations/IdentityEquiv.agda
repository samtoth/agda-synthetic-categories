module foundations.IdentityEquiv where

open import foundations.Universes
open import foundations.Identity
open import foundations.QuasiIsomorphism
open import foundations.CoherentIsomorphism
open import foundations.Sigma
open import foundations.Embedding

sym-qiso : ∀ {𝓤} {A : Type 𝓤} {a b : A} → quasi-iso (sym {x = a} {b})
sym-qiso .fst = sym
sym-qiso .snd .fst refl = refl
sym-qiso .snd .snd refl = refl

sym-is-equiv : ∀ {𝓤} {A : Type 𝓤} {a b : A} → is-equiv (sym {x = a} {b})
sym-is-equiv = is-equiv←qiso sym-qiso

sym≃ : ∀ {𝓤} {A : Type 𝓤} {a b : A} → (a ＝ b) ≃ (b ＝ a)
sym≃ = mk≃ sym sym-is-equiv

＝-equiv : ∀ {𝓤 𝓥} {A : Type 𝓤} {B : Type 𝓥} → {a b : A}
          → (e : A ≃ B) → (a ＝ b) ≃ (e ._≃_.fwd a ＝ e ._≃_.fwd b)
＝-equiv (mk≃ fwd has-is-eqv) = mk≃ (ap fwd) (is-embedding←is-equiv has-is-eqv)
