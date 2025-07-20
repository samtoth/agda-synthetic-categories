module Ergonomics.PushoutUniv where

open import Foundations.Prelude
open import Core.CanonicalPushouts
open import ufAxioms

open import Ergonomics.Universal
open import Ergonomics.Extensionality
open import Ergonomics.Universal
open Universal
open import Ergonomics.Representation
open import Ergonomics.Auto


record Coconeᵘ {𝓤 𝓥 𝓦 𝓜 𝓝 𝓠} {A : Type 𝓤} {B : Type 𝓥}
                {C : Type 𝓦} {f : A → B} {g : A → C}
                (Q : Type 𝓠)
                ⦃ p-u : Universal (B → Q) 𝓜 ⦄
                ⦃ q-u : Universal (C → Q) 𝓝 ⦄
                : Type (𝓤 ⊔ 𝓠 ⊔ 𝓜 ⊔ 𝓝) where
  constructor mk-coconeU
  open Universal 

  field
    p : p-u .methods
    q : q-u .methods
    filler : p-u .from p ∘ f ~ q-u .from q ∘ g

-- unquoteDecl coconeᵘ-repr≅ coconeᵘ-repr≃ =
--   make-record-repr coconeᵘ-repr≅ coconeᵘ-repr≃ (quote Coconeᵘ)

CoconeU-path→ : ∀ {𝓤 𝓥 𝓦 𝓜 𝓝 𝓠} {A : Type 𝓤} {B : Type 𝓥}
                {C : Type 𝓦} {f : A → B} {g : A → C}
                {Q : Type 𝓠}
                ⦃ p-u : Universal (B → Q) 𝓜 ⦄
                ⦃ q-u : Universal (C → Q) 𝓝 ⦄
               → (c c' : Coconeᵘ {f = f} {g = g} Q)
               → (p : c .Coconeᵘ.p ＝ c' .Coconeᵘ.p)
               → (q : c .Coconeᵘ.q ＝ c' .Coconeᵘ.q)
               → (c .Coconeᵘ.filler ~∙ happly (ap (from q-u) q) ▸ g
                    ~ happly (ap (from p-u) p) ▸ f ~∙ c' .Coconeᵘ.filler)
               → c ＝ c'
CoconeU-path→ (mk-coconeU p q filler) (mk-coconeU p q filler')
  refl refl h = ap (mk-coconeU p q) (funext→ ((~∙-reflr _ ~⁻¹) ~∙ h))
              

Cocone←universal : ∀ {𝓤 𝓥 𝓦 𝓜 𝓝 𝓠} {A : Type 𝓤} {B : Type 𝓥}
                {C : Type 𝓦} {f : A → B} {g : A → C}
                (Q : Type 𝓠)
                ⦃ p-u : Universal (B → Q) 𝓜 ⦄
                ⦃ q-u : Universal (C → Q) 𝓝 ⦄
                → Coconeᵘ {f = f} {g = g} Q → Cocone (mk-span A f g) Q
Cocone←universal Q (mk-coconeU p q eq) = mk-cocone (rec! p) (rec! q) eq

Cocone←universal-is-equiv : ∀ {𝓤 𝓥 𝓦 𝓜 𝓝 𝓠} {A : Type 𝓤} {B : Type 𝓥}
                  {C : Type 𝓦} {f : A → B} {g : A → C}
                  (Q : Type 𝓠)
                  ⦃ p-u : Universal (B → Q) 𝓜 ⦄
                  ⦃ q-u : Universal (C → Q) 𝓝 ⦄
                → is-equiv (Cocone←universal {f = f} {g = g} Q)
Cocone←universal-is-equiv {f = f} {g = g} Q ⦃ p-u ⦄ ⦃ q-u ⦄ = is-equiv←qiso iso where
  lem : ∀ {𝓤} {A : Type 𝓤} {a b c d : A}
          (p p' : a ＝ b) (q : b ＝ c) (r : d ＝ c) (s : d ＝ c)
          → p ＝ p'
          → r ＝ s
          → (p ∙ q ∙ sym r) ∙ s ＝ p' ∙ q
  lem p p' refl r s u t
    = ap (λ a → (a ∙ sym r) ∙ s) u ∙ ∙.pulll _ (sym (ap (sym r ∙_) t) ∙ ∙-sym' r)

  iso : quasi-iso (Cocone←universal Q)
  iso .fst (mk-cocone p q filler)
    = mk-coconeU (Univ← auto! p) (Univ← auto! q)
              λ x → happly (Univ≃.ε auto! p) _ ∙ filler x ∙ sym (happly (Univ≃.ε auto! q) _) 
  iso .snd .fst a = CoconeU-path→ _ a (Univ≃.η p-u _) (Univ≃.η q-u _) 
   λ x → lem (happly (Univ≃.ε auto! _) (f x))
          (happly (ap (from p-u) (Univ≃.η p-u _)) (f x))
          (a .Coconeᵘ.filler x)
          (happly (Univ≃.ε q-u _) (g x))
          (happly (ap (from q-u) (Univ≃.η q-u _)) (g x))
          (ap (λ p → happly p (f x)) (sym (Univ≃.coherent p-u (a .Coconeᵘ.p))))
          (ap (λ p → happly p (g x)) (sym (Univ≃.coherent q-u (a .Coconeᵘ.q)))) 

  iso .snd .snd cc = Cocone-path→ _ cc (Univ≃.ε auto! _) (Univ≃.ε auto! _)
   λ a → ((happly (Univ≃.ε auto! p) (f a)
        ∙ (filler a ∙ (sym (happly (Univ≃.ε auto! q) (g a)))))
        ∙  happly (Univ≃.ε auto! q) (g a)) ＝⟨ ap (_∙ happly (Univ≃.ε auto! q) (g a))
                                              (sym (∙-assoc (happly (Univ≃.ε auto! p) (f a))
                                                    (filler a) _)) ⟩
      ((happly (Univ≃.ε auto! p) (f a)
        ∙ filler a) ∙ sym (happly (Univ≃.ε auto! q) (g a)))
        ∙  happly (Univ≃.ε auto! q) (g a) ＝⟨ ∙.cancell _ (∙-sym'
                                               (happly (Univ≃.ε auto! q) (g a))) ⟩
      happly (Univ≃.ε auto! p) (f a) ∙ filler a ∎ where open Cocone cc


Cocone≃universal : ∀ {𝓤 𝓥 𝓦 𝓜 𝓝 𝓠} {A : Type 𝓤} {B : Type 𝓥}
                  {C : Type 𝓦} {f : A → B} {g : A → C}
                  {Q : Type 𝓠}
                  ⦃ p-u : Universal (B → Q) 𝓜 ⦄
                  ⦃ q-u : Universal (C → Q) 𝓝 ⦄
                  → Coconeᵘ {f = f} {g = g} Q ≃ Cocone (mk-span A f g) Q
Cocone≃universal = mk≃ (Cocone←universal _) (Cocone←universal-is-equiv _)


instance
  Universal-Po : ∀ {𝓤 𝓥 𝓦 𝓜 𝓝 𝓠} {A : Type 𝓤} {B : Type 𝓥} {C : Type 𝓦}
                   {f : A → B} {g : A → C} {Q : Type 𝓠}
                   ⦃ _ : Universal (B → Q) 𝓜 ⦄
                   ⦃ _ : Universal (C → Q) 𝓝 ⦄
                 → Universal (Pushout f g → Q) (𝓜 ⊔ 𝓝 ⊔ 𝓤 ⊔ 𝓠)
  Universal-Po {Q = Q} .Universal.methods = Coconeᵘ Q
  Universal-Po .Universal.from = pushout-rec ∘ Cocone←universal _
  Universal-Po {f = f} {g = g} {Q} .Universal.from-is-equiv
    = is-equiv-∘ pushout-rec-is-equiv (Cocone←universal-is-equiv Q)
    
