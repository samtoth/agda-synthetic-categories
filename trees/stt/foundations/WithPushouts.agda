
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
    {-# INLINE span #-}

  open large-pushout (P span) public
  
  module _ {𝓠} (Q : Pushout → Type 𝓠)
           (p : (b : B) → Q (ι₁ b)) (q : (c : C) → Q (ι₂ c))
           (eq : ∀ c → tr Q (filler c) (p (f c)) ＝ q (g c)) where
           
    open is-equiv (has-is-pushoutᵈ {Q = Q})

    private
      M-cocone : CoconeD span cocone Q
      M-cocone = mk-coconeD p q eq

    pushout-ind : (x : Pushout) → Q x
    pushout-ind = bwd M-cocone

    pushout-indβ1 : ∀ x → pushout-ind (ι₁ x) ＝ p x
    pushout-indβ1 = happly (ap CoconeD.p (ε M-cocone))

    pushout-indβ2 : ∀ x → pushout-ind (ι₂ x) ＝ q x
    pushout-indβ2 = happly (ap CoconeD.q (ε M-cocone))

  -- pushout-ind-apβ : 
  
  module _ {𝓠} (Q : Type 𝓠)
           (p : B → Q) (q : C → Q)
           (eq : ∀ c → (p (f c)) ＝ q (g c)) where

    private
      Q-cocone : Cocone span Q
      Q-cocone = mk-cocone p q eq

    eq' : (c : A) → tr _ (filler c) (p (f c)) ＝ q (g c)
    eq' c = tr-constant {A = Q} (filler c) _ ∙ eq c

    pushout-rec : Pushout → Q
    pushout-rec = pushout-ind _ p q eq'

    pushout-recβ1 : ∀ x → pushout-rec (ι₁ x) ＝ p x
    pushout-recβ1 = pushout-indβ1 _ p q eq'

    pushout-recβ2 : ∀ x → pushout-rec (ι₂ x) ＝ q x
    pushout-recβ2 = pushout-indβ2 _ p q eq'

    -- the following type is a bit complicated because we
    -- do not (necesarily) have strictly computing β-laws
    -- so we have to transport over this equality
    pushout-rec-ap : ∀ {x : A}
      → IdP id
         (ap (pushout-rec ) (filler x))
           (ap₂ (_＝_) (pushout-recβ1 (f x)) (pushout-recβ2 (g  x)))
         (eq x)
    pushout-rec-ap = {!ε Q-cocone!}
