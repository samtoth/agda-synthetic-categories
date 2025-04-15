
open import foundations.Pushout

module foundations.PushoutFromEquiv where

open import foundations.Universes
open import foundations.Identity
open import foundations.DependentIdentity
open import foundations.Functions
open import foundations.Sigma
open import foundations.SigmaPath
open import foundations.CoherentIsomorphism
open import foundations.DependentHomotopy


-- module _ {𝓤 𝓥 𝓦} {A : Type 𝓤} {B : Type 𝓥} {C : Type 𝓦}
--           (f : A → B) (g : A → C) where

--   private
--     span : Span 𝓤 𝓥 𝓦
--     span = mk-span A f g
--     {-# INLINE span #-}

--   open large-pushout (P span) public
  
--   module _ {𝓠} (Q : Pushout → Type 𝓠)
--            (p : (b : B) → Q (ι₁ b)) (q : (c : C) → Q (ι₂ c))
--            (eq : ∀ c → IdP Q (p (f c)) (filler c) (q (g c))) where
           
--     open is-equiv (has-is-pushoutᵈ {Q = Q})

--     private
--       M-cocone : CoconeD span cocone Q
--       M-cocone = mk-coconeD p q eq

--     pushout-ind : (x : Pushout) → Q x
--     pushout-ind = bwd M-cocone

--     pushout-indβ1 : ∀ x → pushout-ind (ι₁ x) ＝ p x
--     pushout-indβ1 = happly (ap CoconeD.p (ε M-cocone))

--     pushout-indβ2 : ∀ x → pushout-ind (ι₂ x) ＝ q x
--     pushout-indβ2 = happly (ap CoconeD.q (ε M-cocone))


--     pushout-ind-apβ : ∀ (c : A)
--                      → IdP (λ z → IdP Q (z .CoconeD.p (f c)) (filler c) (z .CoconeD.q (g c)))
--                            (apᵈ pushout-ind (filler c))
--                              (ε M-cocone)
--                            (eq c)
--     pushout-ind-apβ x = happlyᵈ {C = λ z c → IdP Q (z .CoconeD.p (f c)) (filler c) (z .CoconeD.q (g c))}
--                           (ε M-cocone) (apᵈ CoconeD.filler (ε M-cocone)) x  

  
--   module _ {𝓠} {Q : Type 𝓠}
--            (p : B → Q) (q : C → Q)
--            (eq : ∀ c → (p (f c)) ＝ q (g c)) where

--     open is-equiv (has-is-pushoutᵈ {Q = λ _ → Q})

--     private
--       Q-cocone : Cocone span Q
--       Q-cocone = mk-cocone p q eq

--     private
--       M-cocone : CoconeD span cocone (λ _ → Q)
--       M-cocone = mk-coconeD p q eq

--     pushout-rec : Pushout → Q
--     pushout-rec = pushout-ind _ p q eq

--     pushout-recβ1 : ∀ x → pushout-rec (ι₁ x) ＝ p x
--     pushout-recβ1 = pushout-indβ1 _ p q eq

--     pushout-recβ2 : ∀ x → pushout-rec (ι₂ x) ＝ q x
--     pushout-recβ2 = pushout-indβ2 _ p q eq

--     pushout-rec-ap : ∀ (x : A)
--       → IdP (λ z → z .CoconeD.p (f x) ＝ z .CoconeD.q (g x))
--          (ap (pushout-rec ) (filler x))
--            (ε (M-cocone))
--          (eq x)
--     pushout-rec-ap x = pushout-ind-apβ (λ _ → Q) p q eq x 

