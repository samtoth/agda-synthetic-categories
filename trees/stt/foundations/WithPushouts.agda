
open import foundations.Pushout

module foundations.WithPushouts (P : global-pushouts) where

open import foundations.universe
open import foundations.Identity
open import foundations.DependentIdentity
open import foundations.Functions
open import foundations.Sigma
open import foundations.CoherentIsomorphism


module _ {𝓤 𝓥 𝓦} {A : Type 𝓤} {B : Type 𝓥} {C : Type 𝓦}
          (f : A → B) (g : A → C) where

  private
    span : Span 𝓤 𝓥 𝓦
    span = mk-span A f g

  open large-pushout (P span) public
  

  pushout-ind : ∀ {𝓠} {Q : Pushout → Type 𝓠}
                → (p : (b : B) → Q (ι₁ b)) → (q : (c : C) → Q (ι₂ c))
                → (∀ c → tr Q (filler c) (p (f c)) ＝ q (g c))
                → (p : Pushout) → Q p
  pushout-ind {Q = Q} p q eq = bwd (mk-coconeD p q eq) where
    open is-equiv (P span .large-pushout.has-is-pushoutᵈ {Q = Q})


  pushout-rec : ∀ {𝓠} {Q : Type 𝓠}
                → (p : B → Q) → (q : C → Q)
                → (∀ c → p (f c) ＝ q (g c))
                → Pushout → Q
  pushout-rec {Q = Q} p q eq po = pushout-ind p q (λ c → tr-constant {A = Q} (filler c) _ ∙ eq c) po 

  pushout-indβ1 : ∀ {𝓠} {Q : Pushout → Type 𝓠}
                → {p : (b : B) → Q (ι₁ b)} → {q : (c : C) → Q (ι₂ c)}
                → {eq : ∀ c → tr Q (filler c) (p (f c)) ＝ q (g c)} → 
                  ∀ x → pushout-ind p q eq (ι₁ x) ＝ p x
  pushout-indβ1 x = {!!}

