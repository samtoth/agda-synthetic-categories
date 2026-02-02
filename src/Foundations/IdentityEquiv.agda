module Foundations.IdentityEquiv where

open import Foundations.Universes
open import Foundations.Identity
open import Foundations.QuasiIsomorphism
open import Foundations.CoherentIsomorphism
open import Foundations.Homotopy
open import Foundations.Sigma
open import Foundations.Embedding
open import Foundations.EquivHomotopy

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

∙-is-equiv : ∀ {𝓤} {A : Type 𝓤} {a b c : A} (p : a ＝ b)
             → is-equiv (λ (q : b ＝ c) → p ∙ q)
∙-is-equiv refl = id-is-equiv

∙-is-equiv' : ∀ {𝓤} {A : Type 𝓤} {a b c : A} (p : b ＝ c)
             → is-equiv (λ (q : a ＝ b) → q ∙ p)
∙-is-equiv' refl = homotopy-is-equiv (λ where refl → refl) id-is-equiv

＝-postcomp-≃ : ∀ {𝓤} {A : Type 𝓤} {a b c : A} (p : a ＝ b)
               → (b ＝ c) ≃ (a ＝ c)
＝-postcomp-≃ p = mk≃ (λ q → p ∙ q) (∙-is-equiv p)

tr-is-equiv : ∀ {𝓤 𝓥} {A : Type 𝓤} {B : A → Type 𝓥}
                {a b : A} (p : a ＝ b)
              → is-equiv (tr B p)
tr-is-equiv refl = id-is-equiv

