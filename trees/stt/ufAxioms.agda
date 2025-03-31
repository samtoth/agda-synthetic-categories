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

  global-funext : FunExtGlobal


private module fe {𝓤} {𝓥} = WithFunExt {𝓤} {𝓥} global-funext
open fe public

open import foundations.EquivSingleton global-funext public 


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




open import foundations.Pushout public


module _ {𝓤 𝓥 𝓦} {A : Type 𝓤} {B : Type 𝓥} {C : Type 𝓦} where
  postulate 
    Pushout : ∀ (f : A → B) (g : A → C) → Type (𝓤 ⊔ 𝓥 ⊔ 𝓦)

    ι₁ : ∀ {f : A → B} {g : A → C} → B → Pushout f g

    ι₂ :  ∀ {f : A → B} {g : A → C} → C → Pushout f g

    glue : ∀ {f : A → B} {g : A → C} → (x : A) → Id (Pushout f g) (ι₁ (f x)) (ι₂ (g x))

  po-cocone : ∀ {f : A → B} {g : A → C} → Cocone (mk-span _ f g) (Pushout f g)
  po-cocone = mk-cocone ι₁ ι₂ glue

  postulate
    pushout-ind : ∀ {f : A → B} {g : A → C} {𝓠} (Q : Pushout f g → Type 𝓠)
                  → CoconeD (mk-span _ f g) po-cocone Q → (x : Pushout f g) → Q x

  pushout-indβ1 : ∀ {f : A → B} {g : A → C} {𝓠} {Q : Pushout f g → Type 𝓠} →
                    {c : CoconeD (mk-span _ f g) po-cocone Q} →
                     ∀ x → pushout-ind Q c (ι₁ x) ＝ c .CoconeD.p x
  pushout-indβ1 {c = c} x = primEraseEquality eq where
    postulate eq : pushout-ind _ _ (ι₁ x) ＝ c .CoconeD.p x

  pushout-indβ2 : ∀ {f : A → B} {g : A → C} {𝓠} {Q : Pushout f g → Type 𝓠} →
                    {c : CoconeD (mk-span _ f g) po-cocone Q} →
                      ∀ x → pushout-ind Q c (ι₂ x) ＝ c .CoconeD.q x
  pushout-indβ2 {c = c} x = primEraseEquality eq where
    postulate eq : pushout-ind _ _ (ι₂ x) ＝ c .CoconeD.q x

  {-# REWRITE pushout-indβ1 pushout-indβ2 #-}

  pushout-ind-apβ : ∀ {f : A → B} {g : A → C} {𝓠} {Q : Pushout f g → Type 𝓠}
                      {c : CoconeD (mk-span _ f g) po-cocone Q} →
                       ∀ x → apᵈ (pushout-ind Q c) (glue x) ＝ c .CoconeD.filler x
  pushout-ind-apβ {c = c} x = primEraseEquality eq where postulate eq : apᵈ (pushout-ind _ c) (glue x) ＝ c .CoconeD.filler x



  {-# REWRITE pushout-ind-apβ #-}

  opaque 
    pushout-rec : ∀ {f : A → B} {g : A → C} {𝓠} {Q : Type 𝓠}
                  → (c : Cocone (mk-span _ f g) Q)
                  → (p : Pushout f g) → Q
    pushout-rec cc = pushout-ind _ (mk-coconeD p q λ a → tr-constant _ _ ∙ filler a) where open Cocone cc

    pushout-recβ1 : ∀ {f : A → B} {g : A → C} {𝓠} {Q : Type 𝓠}
                   → {c : Cocone (mk-span _ f g) Q}
                   → ∀ l → pushout-rec c (ι₁ l) ＝ c .Cocone.p l
    pushout-recβ1 l = refl

    pushout-recβ2 : ∀ {f : A → B} {g : A → C} {𝓠} {Q : Type 𝓠}
                   → {c : Cocone (mk-span _ f g) Q}
                   → ∀ r → pushout-rec c (ι₂ r) ＝ c .Cocone.q r
    pushout-recβ2 l = refl

  {-# REWRITE pushout-recβ1 pushout-recβ2 #-}

  opaque 
    unfolding pushout-rec
    pushout-rec-apβ : ∀ {f : A → B} {g : A → C} {𝓠} {Q : Type 𝓠}
                      → {c : Cocone (mk-span _ f g) Q}
                      → ∀ x → ap (pushout-rec c) (glue x)
                                ＝ c .Cocone.filler x
    pushout-rec-apβ {f = f} {g = g}{c = c} x =  sym (sym (filler-lem {c = c} x) ∙ apᵈ-is-ap ) where
      filler-lem : ∀ {f : A → B} {g : A → C} {𝓠} {Q : Type 𝓠}
                    {c : Cocone (mk-span _ f g) Q} →
                    ∀ x → (tr-constant (glue {f} {g} x) _ ∙ c .Cocone.filler x)
                                       ＝[ ap (_＝ Cocone.q c (g x)) (tr-constant _ _) ]
                          c .Cocone.filler x
      filler-lem {f = f} {g = g} {Q = Q}{c = c} x = ?

  {-# REWRITE pushout-rec-apβ #-}


  pushout-ind-is-equiv : ∀ {f : A → B} {g : A → C}
                         {𝓠} {Q : Pushout f g → Type 𝓠}
                         → is-equiv (pushout-ind Q)
  pushout-ind-is-equiv {f} {g} {Q = Q} = is-equiv←qiso I where

   s : ((p : Pushout f g) → Q p) → CoconeD (mk-span _ f g) po-cocone Q
   s f = mk-coconeD (f ∘ ι₁) (f ∘ ι₂) (apᵈ f ∘ glue)

   I : quasi-iso (pushout-ind Q)
   I .fst f = s f 
   I .snd .fst (mk-coconeD p q filler) = refl
   I .snd .snd f = funext→ (pushout-ind (λ z → (pushout-ind _ ∘ s) f z ＝ f z)
                   (mk-coconeD ~refl ~refl λ a → {! drop-i (apᵈ f (glue a)) !} ))



pushout-rec-is-equiv : ∀ {𝓤 𝓥 𝓦} {A : Type 𝓤}{B : Type 𝓥}
                       {C : Type 𝓦}
                        {f : A → B} {g : A → C} 
                        → is-pushoutω (mk-span _ f g) po-cocone
pushout-rec-is-equiv {A = A} {f = f} {g} {Q = Q} = is-equiv←qiso I where
  I : quasi-iso (construct-cocone (mk-span A f g) po-cocone)
  I .fst = pushout-rec
  I .snd .fst fun = funext→ (pushout-ind _ (mk-coconeD ~refl ~refl λ a → {!drop-j!})) 
  I .snd .snd (mk-cocone p q filler) = refl


Pushouts : global-pushouts
Pushouts S = po where
  open Span S

  po : Ind-Pushout S
  po .Ind-Pushout.Pushout = Pushout left right
  po .Ind-Pushout.cocone = po-cocone
  po .Ind-Pushout.pushout-ind = pushout-ind
  po .Ind-Pushout.pushout-indβ1 _ = refl
  po .Ind-Pushout.pushout-indβ2 _ = refl
  po .Ind-Pushout.pushout-ind-apβ _ = refl -- :)




