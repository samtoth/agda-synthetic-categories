module foundations.Subtypes where

open import foundations.Universes
open import foundations.Sigma
open import foundations.Functions
open import foundations.QuasiIsomorphism
open import foundations.CoherentIsomorphism
open import foundations.Identity
open import foundations.Singleton
open import foundations.EquivContrFibre
open import foundations.FibrePath
open import foundations.EquivSingleton
open import foundations.SigmaPath
open import foundations.FunextUnivalence


is-subtype : ∀ {𝓤 𝓥} {A : Type 𝓤} (P : A → Type 𝓥) → Type _
is-subtype P = ∀ x → is-prop (P x)

record Subtype {𝓤} (A : Type 𝓤) 𝓥 : Type (𝓤 ⊔ lsuc 𝓥) where
  constructor mk-subtype
  field
    {family} : A → Type 𝓥
    has-is-subtype : is-subtype family

module _ {𝓤} {A : Type 𝓤} {𝓥} (P : Subtype A 𝓥) where
  open Subtype P

  Σ̃ : Type _
  Σ̃ = Σ A family

  Σ̃-π : Σ̃ → A
  Σ̃-π = fst

  Σ̃-π-emb : is-prop-map Σ̃-π 
  Σ̃-π-emb a = is-prop←equiv-to-prop
               (fibre-straighten _ _ e⁻¹)
               (has-is-subtype a)


