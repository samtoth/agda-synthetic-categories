module ufAxioms where

open import foundations.Prelude

-- !!CAUTION!! - this is not in general sound with --without-K - use with caution.
primitive
  primEraseEquality : {𝓤 : Level} {A : Type 𝓤} {x y : A} → x ＝ y → x ＝ y

open import foundations.FunExt


postulate
  weak-funext : ∀ {𝓤 𝓥} {A : Type 𝓤} {B : A → Type 𝓥}
                → (∀ a → is-singleton (B a))
                → is-singleton ((a : A) → B a)

  global-funext : FunExt-global


private module fe = WithFunExt-global global-funext
open fe public

import foundations.CanonicalPullbacks
open foundations.CanonicalPullbacks.WithFunExt global-funext public
import foundations.PathSplit
open foundations.PathSplit.PSWithFunExt global-funext public
open import foundations.EquivProp global-funext public
open import foundations.EmptyUP global-funext public
open import foundations.SingletonClosure public hiding (Singleton-Π)
open import foundations.PropClosure public hiding (is-prop-Π)
open import foundations.SingletonProp global-funext public
open import foundations.CompositionEquiv global-funext public
open import foundations.CompositionFibres global-funext public
Singleton-Π = weak-funext
is-prop-Π : ∀ {𝓤 𝓥 : Level} {A : Type 𝓤} {B : A → Type 𝓥}
            → ((a : A) → is-prop (B a))
            → is-prop (Π A B)
is-prop-Π = foundations.PropClosure.is-prop-Π global-funext

funext-redex : ∀ {𝓤 𝓥} {A : Type 𝓤} {B : A → Type 𝓥}
               { f g : (a : A) → B a } → {p : f ~ g}
               → happly (funext→ p) ＝ p
funext-redex {p = p} = is-equiv.ε global-funext p

{-# REWRITE funext-redex #-}


open import foundations.Univalence

postulate
  UA : Univalence


open WithGlobalUnivalence UA public

{-# REWRITE ua-linv #-}

open import foundations.PropExt public using (PropExt)
import foundations.PropExt as PE

propExt : ∀ {𝓤} → PropExt 𝓤
propExt = PE.PropExt←Univalence global-funext UA

open import foundations.Pushout public
import foundations.Span as Sp

Cocone-path→ : ∀ {𝓤 𝓥 𝓦} {S : Span 𝓤 𝓥 𝓦} {𝓛} {X : Type 𝓛}
               → (c c' : Cocone S X)
               → (p : c .Cocone.p ＝ c' .Cocone.p)
               → (q : c .Cocone.q ＝ c' .Cocone.q)
               → (c .Cocone.filler ~∙ happly q ▸ S .Span.right
                    ~ happly p ▸ S .Span.left ~∙ c' .Cocone.filler)
               → c ＝ c'
Cocone-path→ = Sp.Cocone-path→ global-funext


open import foundations.DependentCocone


module _ {𝓤 𝓥 𝓦} {A : Type 𝓤} {B : Type 𝓥} {C : Type 𝓦} where
  postulate
    Pushout : ∀ (f : A → B) (g : A → C) → Type (𝓤 ⊔ 𝓥 ⊔ 𝓦)

    ι₁ : ∀ {f : A → B} {g : A → C} → B → Pushout f g

    ι₂ :  ∀ {f : A → B} {g : A → C} → C → Pushout f g

    glue : ∀ {f : A → B} {g : A → C} → ι₁ {f} {g} ∘ f ~ ι₂ ∘ g

  pushout : ∀ {f : A → B} {g : A → C} → Cocone (mk-span _ f g) (Pushout f g)
  pushout = mk-cocone ι₁ ι₂ glue

  postulate
    pushout-ind : ∀ {f : A → B} {g : A → C} {𝓠} (Q : Pushout f g → Type 𝓠)
                  → CoconeD (mk-span _ f g) pushout Q → (x : Pushout f g) → Q x

  pushout-indβ1 : ∀ {f : A → B} {g : A → C} {𝓠} {Q : Pushout f g → Type 𝓠} →
                    {c : CoconeD (mk-span _ f g) pushout Q} →
                     ∀ x → pushout-ind Q c (ι₁ x) ＝ c .CoconeD.p x
  pushout-indβ1 {c = c} x = primEraseEquality eq where
    postulate eq : pushout-ind _ _ (ι₁ x) ＝ c .CoconeD.p x

  pushout-indβ2 : ∀ {f : A → B} {g : A → C} {𝓠} {Q : Pushout f g → Type 𝓠} →
                    {c : CoconeD (mk-span _ f g) pushout Q} →
                      ∀ x → pushout-ind Q c (ι₂ x) ＝ c .CoconeD.q x
  pushout-indβ2 {c = c} x = primEraseEquality eq where
    postulate eq : pushout-ind _ _ (ι₂ x) ＝ c .CoconeD.q x

  {-# REWRITE pushout-indβ1 pushout-indβ2 #-}

  pushout-ind-apβ : ∀ {f : A → B} {g : A → C} {𝓠} {Q : Pushout f g → Type 𝓠}
                      {c : CoconeD (mk-span _ f g) pushout Q} →
                       ∀ x → apᵈ (pushout-ind Q c) (glue x) ＝ c .CoconeD.filler x
  pushout-ind-apβ {c = c} x = primEraseEquality eq where
    postulate eq : apᵈ (pushout-ind _ c) (glue x) ＝ c .CoconeD.filler x

  opaque
    pushout-rec : ∀ {f : A → B} {g : A → C} {𝓠} {Q : Type 𝓠}
                  → Cocone (mk-span _ f g) Q
                  → Pushout f g → Q
    pushout-rec {Q = Q} cc@(mk-cocone p q h)
      = pushout-ind (λ _ → Q) (Dependent←Cocone {P = λ _ → Q} cc)

    pushout-recβ1 : ∀ {f : A → B} {g : A → C} {𝓠} {Q : Type 𝓠}
                    → {c : Cocone (mk-span _ f g) Q}
                    → ∀ x → pushout-rec c (ι₁ x) ＝ c .Cocone.p x
    pushout-recβ1 _ = refl

    pushout-recβ2 : ∀ {f : A → B} {g : A → C} {𝓠} {Q : Type 𝓠}
                    → {c : Cocone (mk-span _ f g) Q}
                    → ∀ x → pushout-rec c (ι₂ x) ＝ c .Cocone.q x
    pushout-recβ2 _ = refl

  {-# REWRITE pushout-recβ1 pushout-recβ2 #-}

  opaque
    unfolding pushout-rec
    pushout-rec-apβ : ∀ {f : A → B} {g : A → C} {𝓠} {Q : Type 𝓠}
                      {c : Cocone (mk-span _ f g)  Q} →
                       ∀ x → ap (pushout-rec c) (glue x) ＝ c .Cocone.filler x
    pushout-rec-apβ {f} {g} {Q = Q} {c} x
      = ap (pushout-rec _) (glue x)                      ＝⟨ sym apᵈ-is-ap ⟩
        coe (tr-cst ∙-) (apᵈ (pushout-rec c) (glue x))   ＝⟨ ap (coe (tr-cst ∙-)) (pushout-ind-apβ x) ⟩
        coe (tr-cst ∙-)
          (CoconeD.filler {cc = pushout}
            (Dependent←Cocone {P = λ _ → Q} c) x)        ＝⟨⟩
        coe (tr-cst ∙-) (tr-cst ∙ (c .Cocone.filler x))  ＝⟨ coe-postcomp＝ tr-cst _ ⟩
        sym tr-cst ∙ (tr-cst ∙ (c .Cocone.filler x))     ＝⟨ ∙.cancelr _ {h = tr-cst} (∙-sym' tr-cst) {f = c .Cocone.filler x} ⟩
        Cocone.filler c x ∎ where
         tr-cst : tr (λ _ → Q) (glue {f = f} {g} x) (pushout-rec c (ι₁ (f x))) ＝ pushout-rec c (ι₁ (f x))
         tr-cst = tr-constant (glue x) (pushout-rec c (ι₁ (f x)))
