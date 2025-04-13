module ergonomics.PushoutUniv where

open import foundations.Prelude
open import ufAxioms

open import ergonomics.Universal
open import ergonomics.Extensionality


-- record CoconeDᵘ {𝓤 𝓥 𝓦 𝓜 𝓝 𝓠} {A : Type 𝓤} {B : Type 𝓥}
--                 {C : Type 𝓦} {f : A → B} {g : A → C}
--                 (Q : Pushout f g → Type 𝓠)
--                 ⦃ p-u : Universal ((b : B) → Q (ι₁ b)) 𝓜 ⦄
--                 ⦃ q-u : Universal ((c : C) → Q (ι₂ c)) 𝓝 ⦄
--                 : Type (𝓤 ⊔ 𝓠 ⊔ 𝓜 ⊔ 𝓝) where
--   constructor mk-coconeU
--   open Universal 

--   field
--     p : p-u .methods
--     q : q-u .methods
--     eq : (x : A) → PathP (λ i → Q (glue x $ i)) (p-u .from p (f x)) (q-u .from q (g x)) 


-- record CoconeDᵘ-path   {𝓤 𝓥 𝓦 𝓜 𝓝 𝓠} {A : Type 𝓤} {B : Type 𝓥}
--                        {C : Type 𝓦} {f : A → B} {g : A → C}
--                        (Q : Pushout f g → Type 𝓠)
--                        ⦃ p-u : Universal ((b : B) → Q (ι₁ b)) 𝓜 ⦄
--                        ⦃ q-u : Universal ((c : C) → Q (ι₂ c)) 𝓝 ⦄
--                        (CA CB : CoconeDᵘ Q) : Type (𝓤 ⊔ 𝓠 ⊔ 𝓜 ⊔ 𝓝) where
--   module CA = CoconeDᵘ CA
--   module CB = CoconeDᵘ CB
--   open Universal {{...}}
--   field
--     p-eq : Path _ CA.p CB.p
--     q-eq : Path _ CA.q CB.q
--     filler-eq : ∀ x → PathP (λ i → PathP (λ j → Q (glue x $ j)) (from (p-eq $ i) (f x)) (from (q-eq $ i) (g x)))
--                        (CA.eq x) (CB.eq x)

-- CoconeDᵘ-from-path : ∀ {𝓤 𝓥 𝓦 𝓜 𝓝 𝓠} {A : Type 𝓤} {B : Type 𝓥}
--                        {C : Type 𝓦} {f : A → B} {g : A → C}
--                        {Q : Pushout f g → Type 𝓠}
--                        ⦃ p-u : Universal ((b : B) → Q (ι₁ b)) 𝓜 ⦄
--                        ⦃ q-u : Universal ((c : C) → Q (ι₂ c)) 𝓝 ⦄
--                        {CA CB : CoconeDᵘ Q} → CoconeDᵘ-path Q CA CB
--                        → Path _ CA CB
-- CoconeDᵘ-from-path record { p-eq = p-eq ; q-eq = q-eq ; filler-eq = filler-eq }
--   = toPath (λ i → mk-coconeU (p-eq $ i) (q-eq $ i) (λ x → filler-eq x $ i))

-- CoconeD←universal : ∀ {𝓤 𝓥 𝓦 𝓜 𝓝 𝓠} {A : Type 𝓤} {B : Type 𝓥}
--                      {C : Type 𝓦} {f : A → B} {g : A → C}
--                      (Q : Pushout f g → Type 𝓠)
--                      ⦃ p-u : Universal ((b : B) → Q (ι₁ b)) 𝓜 ⦄
--                      ⦃ q-u : Universal ((c : C) → Q (ι₂ c)) 𝓝 ⦄
--                      → CoconeDᵘ Q → CoconeD (mk-span _ f g) po-cocone Q
-- CoconeD←universal Q (mk-coconeU p q eq) = mk-coconeD (ind! p) (ind! q) eq

-- CoconeD←universal-equiv : ∀ {𝓤 𝓥 𝓦 𝓜 𝓝 𝓠} {A : Type 𝓤} {B : Type 𝓥}
--                      {C : Type 𝓦} {f : A → B} {g : A → C}
--                      (Q : Pushout f g → Type 𝓠)
--                      ⦃ p-u : Universal ((b : B) → Q (ι₁ b)) 𝓜 ⦄
--                      ⦃ q-u : Universal ((c : C) → Q (ι₂ c)) 𝓝 ⦄
--                      → is-equiv (CoconeD←universal Q)
-- CoconeD←universal-equiv {f = f} {g = g} Q ⦃ p-u ⦄ ⦃ q-u ⦄ = is-equiv←qiso lem where
--   module pu = Universal p-u
--   module qu = Universal q-u
  
--   lem : quasi-iso (CoconeD←universal Q)
--   lem .fst (mk-coconeD p q filler) = mk-coconeU (Universal.Univ← p-u p) (Universal.Univ← q-u q) λ c
--     → adjust-path (sym (happly (Universal.≃.ε p-u p) (f c))) (sym (happly (Universal.≃.ε q-u q) (g c))) (filler c)
--   lem .snd .fst (mk-coconeU p q eq) = Id←Path (CoconeDᵘ-from-path (record
--     { p-eq = Path←Id (pu.≃.η p) ; q-eq = Path←Id (qu.≃.η q) ; filler-eq = λ x → it })) where postulate it : ∀ {A} → A
--   lem .snd .snd (mk-coconeD p q filler) = Id←Path (Path←CoconeD-Path (record
--     { p-eq = λ l → Path←Id (happly (pu.≃.ε p) l) ; q-eq = λ r → Path←Id (happly (qu.≃.ε q) r) ; filler-eq = it })) where
--       postulate it : ∀ {A} → A

-- instance
--   Universal-Po : ∀ {𝓤 𝓥 𝓦 𝓜 𝓝 𝓠} {A : Type 𝓤} {B : Type 𝓥} {C : Type 𝓦}
--                    {f : A → B} {g : A → C} {Q : Pushout f g → Type 𝓠}
--                    ⦃ _ : Universal ((b : B) → Q (ι₁ b)) 𝓜 ⦄
--                    ⦃ _ : Universal ((c : C) → Q (ι₂ c)) 𝓝 ⦄
--                  → Universal ((p : Pushout f g) → Q p) (𝓜 ⊔ 𝓝 ⊔ 𝓤 ⊔ 𝓠)
--   Universal-Po {Q = Q} .Universal.methods = CoconeDᵘ Q
--   Universal-Po .Universal.from = pushout-ind _ ∘ CoconeD←universal _
--   Universal-Po {f = f} {g = g} {Q} .Universal.from-is-equiv = is-equiv-∘ Pushout-ind-is-equiv (CoconeD←universal-equiv Q)
    
