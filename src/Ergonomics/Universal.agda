module Ergonomics.Universal where

open import Foundations.Prelude
open import ufAxioms

-- Although this is called Universal, really this is kind of
-- a general purpose 'coercion' class. The 'Universal' record
-- type is actually just the Singleton wrt. identity-extensionality.
-- I.e. assuming univalence, Universal A 𝓥 ≃ Σ B : 𝓤, A ＝ B ≃ 𝟙
-- so it is reasonable to ask instance search to do this work for us

-- In order to make instance search actually work, we really define
-- instances for types either of the form `A -> X` where A is a kind
-- of colimit, or `X -> A` where A is a kind of limit.

record Universal {𝓤} (A : Type 𝓤) 𝓥 : Type (𝓤 ⊔ lsuc 𝓥) where
  field
    methods       : Type 𝓥
    from          : methods → A
    from-is-equiv : is-equiv from

  Univ← : A → methods
  Univ← = is-equiv.bwd from-is-equiv

  Univ≃ : methods ≃ A
  Univ≃ = mk≃ from from-is-equiv

  Univ≃' : A ≃ methods
  Univ≃' = Univ≃ e⁻¹

  module Univ≃ = _≃_ (mk≃ from from-is-equiv)

open Universal

Universal←Equiv : ∀ {𝓤 𝓥} {A : Type 𝓤} {B : Type 𝓥}
                → B ≃ A → Universal A 𝓥
Universal←Equiv {A = A} {B} e .methods = B
Universal←Equiv e .from = _≃_.fwd e
Universal←Equiv e .from-is-equiv = _≃_.has-is-eqv e


instance
  -- The basic structural rules allow us to stop recurring (we can
  -- produce an A given an A) and to skip an argument, introducing a
  -- function type into the methods:

  Universal-default : ∀ {𝓤} {A : Type 𝓤} → Universal A 𝓤
  Universal-default .methods = _
  Universal-default .from x  = x
  Universal-default .from-is-equiv = id-is-equiv

  Universal-Π
    : ∀ {𝓤 𝓥 𝓦} {A : Type 𝓤} {B : A → Type 𝓥}
    → ⦃ _ : ∀ {a} → Universal (B a) 𝓦 ⦄
    → Universal (∀ a → B a) (𝓤 ⊔ 𝓦)
  Universal-Π ⦃ u ⦄ .methods = ∀ a → u {a} .methods
  Universal-Π ⦃ u ⦄ .from = u .from ∘_
  Universal-Π {A = A} {B} ⦃ u ⦄ .from-is-equiv
    = postcomp-Π-equiv (u .from-is-equiv)

  {-# INCOHERENT Universal-default #-}
  {-# OVERLAPPABLE Universal-Π #-}

Universal←equiv-to-universal : ∀ {𝓤 𝓥 𝓦} {A : Type 𝓤} {B : Type 𝓥}
                             → A ≃ B
                             → Universal A 𝓦
                             → Universal B 𝓦
Universal←equiv-to-universal eq ua = Universal←Equiv (Univ≃ ua ∙≃ eq)


instance
  Universal-Σ
    : ∀ {𝓤 𝓥 𝓦 𝓛} {A : Type 𝓤} {B : A → Type 𝓥} {C : (x : A) → B x → Type 𝓦}
    → ⦃ _ : Universal ((x : A) (y : B x) → C x y) 𝓛 ⦄
    → Universal ((x : Σ A B) → C (x .fst) (x .snd)) 𝓛
  Universal-Σ ⦃ u ⦄ = Universal←equiv-to-universal uncurry≃ u

  Universal-𝟙
    : ∀ {𝓤 𝓥} {A : Type 𝓤}
      → ⦃ _ : Universal A 𝓥 ⦄
      → Universal (𝟙 → A) 𝓥
  Universal-𝟙 ⦃ u ⦄ = Universal←equiv-to-universal (unit-UP≃ e⁻¹) u

  Universal-⊥
    : ∀ {𝓤} {A : Type 𝓤}
      → Universal (∅ → A) lzero
  Universal-⊥ .methods = 𝟙
  Universal-⊥ .from _  = ¡_
  Universal-⊥ .from-is-equiv = K¡-𝟙-is-equiv


rec! : ∀ {𝓤 𝓥 𝓦} {A : Type 𝓤} {B : Type 𝓥} ⦃ r : Universal (A → B) 𝓦 ⦄ → r .methods → A → B
rec! ⦃ r ⦄ = r .from

ind! : ∀ {𝓤 𝓥 𝓦} {A : Type 𝓤} {B : A → Type 𝓥} ⦃ r : Universal (∀ x → B x) 𝓦 ⦄ → r .methods → ∀ x → B x
ind! ⦃ r ⦄ = r .from

corec! : ∀ {𝓤 𝓥 𝓦} {A : Type 𝓤} {B : Type 𝓥} ⦃ r : Universal (A → B) 𝓦 ⦄ → r .methods → A → B
corec! ⦃ r ⦄ = r .from

coind! : ∀ {𝓤 𝓥 𝓦} {A : Type 𝓤} {B : A → Type 𝓥} ⦃ r : Universal (∀ x → B x) 𝓦 ⦄ → r .methods → ∀ x → B x
coind! ⦃ r ⦄ = r .from
