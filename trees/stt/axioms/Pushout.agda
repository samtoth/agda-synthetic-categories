
module axioms.Pushout where

open import foundations.Prelude
open import axioms.Interval
open import axioms.EraseEquality
open import axioms.FunExt

record Span 𝓤 𝓥 𝓦 : Type (lsuc (𝓤 ⊔ 𝓥 ⊔ 𝓦)) where
  constructor mk-span
  field
    Centre : Type 𝓤
    {Left} : Type 𝓥
    left   : Centre → Left
    {Right} : Type 𝓦
    right : Centre → Right


record Cocone  {𝓤 𝓥 𝓦} (S : Span 𝓤 𝓥 𝓦) {𝓛} (Carrier : Type 𝓛)
        : Type (lsuc (𝓤 ⊔ 𝓥 ⊔ 𝓦 ⊔ 𝓛))  where
  constructor mk-cocone
  open Span S
  field
    p       : Left → Carrier
    q       : Right → Carrier
    filler  : ∀ a → Path Carrier (p (left a)) (q (right a))


record CoconeD {𝓤 𝓥 𝓦} (S : Span 𝓤 𝓥 𝓦)
               {𝓛} {Q : Type 𝓛} (cc : Cocone S Q)
               {𝓜} (P : Q → Type 𝓜) : Type (𝓤 ⊔ 𝓥 ⊔ 𝓦 ⊔ 𝓛 ⊔ 𝓜) where
  constructor mk-coconeD
  open Span S
  open Cocone cc
  field
    p : (l : Left) → P (p l) 
    q : (r : Right) → P (q r)
    filler : ∀ (c : Centre) → PathP (λ i → P (filler c $ i)) (p (left c)) (q (right c)) 

record CoconeD-Path {𝓤 𝓥 𝓦} {S : Span 𝓤 𝓥 𝓦}
                    {𝓠} {Q : Type 𝓠} (cc : Cocone S Q)
                    {𝓜} {P : Q → Type 𝓜} (CA CB : CoconeD S cc P)
                    : Type (𝓤 ⊔ 𝓥 ⊔ 𝓦 ⊔ 𝓠 ⊔ 𝓜) where
  open Span S
  open Cocone cc
  module CA = CoconeD CA
  module CB = CoconeD CB
  field
    p-eq : ∀ l → PathP (λ i → P (p l) ) (CA.p l) (CB.p l)
    q-eq : ∀ r → PathP (λ i → P (q r) ) (CA.q r) (CB.q r)
    filler-eq : ∀ c → PathP (λ i → PathP (λ j → P (filler c $ j)) (p-eq (left c) $ i) (q-eq (right c) $ i))
                        (CA.filler c) (CB.filler c)

Path←CoconeD-Path : ∀ {𝓤 𝓥 𝓦} {S : Span 𝓤 𝓥 𝓦}
                    {𝓠} {Q : Type 𝓠} {cc : Cocone S Q}
                    {𝓜} {P : Q → Type 𝓜} {CA CB : CoconeD S cc P}
                    → CoconeD-Path cc CA CB → Path _ CA CB
Path←CoconeD-Path record { p-eq = p-eq ; q-eq = q-eq ; filler-eq = filler-eq }
  = toPath (λ i → mk-coconeD ((_$ i) ∘ p-eq) ((_$ i) ∘ q-eq) ((_$ i) ∘ filler-eq))
                    

module _ {𝓤 𝓥 𝓦} (S : Span 𝓤 𝓥 𝓦) where
  construct-cocone : ∀ {𝓛 𝓜} {C : Type 𝓛} (C-cc : Cocone S C)
                {Q : Type 𝓜} → (C → Q) → Cocone S Q
  construct-cocone C f = mk-cocone (f ∘ p) (f ∘ q) λ c → toPath (λ i → f (filler c $ i)) where open Cocone C


  is-pushout : ∀ {𝓛} {C : Type 𝓛} → Cocone S C → Type _
  is-pushout {𝓛} C = ∀ {Q : Type (𝓤 ⊔ 𝓥 ⊔ 𝓦 ⊔ 𝓛)} → is-equiv (construct-cocone C {Q})



  construct-coconeᵈ : ∀ {𝓛 𝓜} {C : Type 𝓛} (C-cc : Cocone S C)
                      → {Q : C → Type 𝓜}
                      → ((c : C) → Q c)
                      → CoconeD S C-cc Q 
  construct-coconeᵈ C f = mk-coconeD (f ∘ p) (f ∘ q) λ c → toPath (λ i → f (filler c $ i)) where open Cocone C

  is-pushoutᵈ : ∀ {𝓛} {C : Type 𝓛} → Cocone S C → Type _
  is-pushoutᵈ {𝓛} {C} Cc =  ∀ {Q : C → Type (𝓤 ⊔ 𝓥 ⊔ 𝓦 ⊔ 𝓛)} → is-equiv (construct-coconeᵈ Cc {Q})

  
  is-pushoutωᵈ : ∀ {𝓛} {C : Type 𝓛} → Cocone S C → Typeω
  is-pushoutωᵈ {𝓛} {C} Cc = ∀ {𝓜} {Q : C → Type 𝓜} → is-equiv (construct-coconeᵈ Cc {Q})

has-pushouts : ∀ 𝓤 → Type (lsuc 𝓤)
has-pushouts 𝓤 = ∀ (S : Span 𝓤 𝓤 𝓤)
                  → Σ[ P ∶ Type 𝓤 ] Σ[ C ∶ Cocone S P ]
                       is-pushout S C

record Ind-Pushout {𝓤 𝓥 𝓦} (S : Span 𝓤 𝓥 𝓦) : Typeω where
  open Span S public

  field
    Pushout : Type (𝓤 ⊔ 𝓥 ⊔ 𝓦)
    cocone : Cocone S Pushout

  open Cocone cocone public renaming (p to ι₁ ; q to ι₂ ; filler to glue)

  open CoconeD

  field
    pushout-ind : ∀ {𝓠} (Q : Pushout → Type 𝓠) → CoconeD S cocone Q → (x : Pushout) → Q x

    pushout-indβ1 : ∀ {𝓠} {Q : Pushout → Type 𝓠} → {c : CoconeD S cocone Q} →
                      ∀ x → pushout-ind Q c (ι₁ x) ＝ c .p x

    pushout-indβ2 : ∀ {𝓠} {Q : Pushout → Type 𝓠} → {c : CoconeD S cocone Q} →
                      ∀ x → pushout-ind Q c (ι₂ x) ＝ c .q x

  field
    pushout-ind-apβ : ∀ {𝓠} {Q : Pushout → Type 𝓠} {c : CoconeD S cocone Q}
                      → ∀ x i → pushout-ind Q c (glue x $ i) ＝ (c .filler x $ i)

  -- has-is-pushoutω : is-pushoutωᵈ S cocone
  -- has-is-pushoutω = is-equiv←qiso II where
  --   II : quasi-iso (construct-coconeᵈ S cocone)
  --   II .fst = pushout-ind _
  --   II .snd .fst f = funext→ (pushout-ind (λ z → (pushout-ind _ ∘ construct-coconeᵈ S cocone) f z ＝ f z)
  --                            (mk-coconeD pushout-indβ1 pushout-indβ2
  --                            λ c → toPath (λ i → {!fromPath!})))
  --   II .snd .snd (mk-coconeD p₁ q₁ filler₁) = {!!}



global-pushouts : Typeω
global-pushouts = ∀ {𝓤 𝓥 𝓦} (S : Span 𝓤 𝓥 𝓦) → Ind-Pushout S


module _ {𝓤 𝓥 𝓦} {A : Type 𝓤} {B : Type 𝓥} {C : Type 𝓦} where
  postulate 
    Pushout : ∀ (f : A → B) (g : A → C) → Type (𝓤 ⊔ 𝓥 ⊔ 𝓦)

    ι₁ : ∀ {f : A → B} {g : A → C} → B → Pushout f g

    ι₂ :  ∀ {f : A → B} {g : A → C} → C → Pushout f g

    glue : ∀ {f : A → B} {g : A → C} → (x : A) → Path (Pushout f g) (ι₁ (f x)) (ι₂ (g x))

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
                       ∀ x i → pushout-ind Q c (glue x $ i) ＝ c .CoconeD.filler x $ i
  pushout-ind-apβ {c = c} x i = primEraseEquality eq where postulate eq : pushout-ind _ c (glue x $ i) ＝ c .CoconeD.filler x $ i

  pushout-ind-apβ0 : ∀ {f : A → B} {g : A → C} {𝓠} {Q : Pushout f g → Type 𝓠}
                      {c : CoconeD (mk-span _ f g) po-cocone Q} →
                       ∀ x → pushout-ind Q c (glue x $ i0) ＝ c .CoconeD.p (f x)
  pushout-ind-apβ0 x = refl

  pushout-ind-apβ1 : ∀ {f : A → B} {g : A → C} {𝓠} {Q : Pushout f g → Type 𝓠}
                      {c : CoconeD (mk-span _ f g) po-cocone Q} →
                       ∀ x → pushout-ind Q c (glue x $ i1) ＝ c .CoconeD.q (g x)
  pushout-ind-apβ1 x = refl

  {-# REWRITE pushout-ind-apβ #-}

Pushouts : global-pushouts
Pushouts S = po where
  open Span S

  po : Ind-Pushout S
  po .Ind-Pushout.Pushout = Pushout left right
  po .Ind-Pushout.cocone = po-cocone
  po .Ind-Pushout.pushout-ind = pushout-ind
  po .Ind-Pushout.pushout-indβ1 _ = refl
  po .Ind-Pushout.pushout-indβ2 _ = refl
  po .Ind-Pushout.pushout-ind-apβ _ _ = refl -- :)


Pushout-is-pushout : ∀ {𝓤 𝓥 𝓦} {S : Span 𝓤 𝓥 𝓦} →  is-pushoutωᵈ S po-cocone
Pushout-is-pushout =  is-equiv←qiso ((pushout-ind _) , ret , sec) where
  ret : retract-witness (construct-coconeᵈ _ po-cocone) (pushout-ind _)
  ret a = funext→ (pushout-ind (λ z →
                                  (pushout-ind _ ∘
                                   construct-coconeᵈ _ po-cocone) a z
                                  ＝ a z) (mk-coconeD ~refl ~refl (λ c → path-drop-j (λ i → a (glue c $ i)))))

  sec : section-witness (construct-coconeᵈ _ po-cocone) (pushout-ind _)
  sec a = refl

Pushout-ind-is-equiv : ∀ {𝓤 𝓥 𝓦 𝓛} {S : Span 𝓤 𝓥 𝓦} {Q : Pushout (S .Span.left) (S .Span.right) → Type 𝓛}
                     → is-equiv (pushout-ind Q)
Pushout-ind-is-equiv = is-equiv-bwd Pushout-is-pushout
