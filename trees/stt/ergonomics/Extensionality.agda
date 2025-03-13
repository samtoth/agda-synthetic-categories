module ergonomics.Extensionality where

open import foundations.Prelude
open import foundations.IdentitySystem
open import foundations.Subtypes
open import foundations.EquivContrFibre

open import ufAxioms
open Identity-system public 

instance
  IdS-default : ∀ {𝓤} {A : Type 𝓤} → Identity-system A 𝓤
  IdS-default .IdS = _＝_
  IdS-default .IdS₀ = refl
  IdS-default .has-is-ids a
    = is-identity-system←Sing-sing (a ＝_) refl Sing-is-singleton

{-# INCOHERENT IdS-default #-}

instance
  IdS-Π : ∀ {𝓤 𝓥 𝓦} {A : Type 𝓤} {B : A → Type 𝓥}
          → ⦃ _ : ∀ {a} → Identity-system (B a) 𝓦 ⦄
          → Identity-system ((a : A) → B a) (𝓤 ⊔ 𝓦)
  IdS-Π ⦃ s ⦄ .IdS f g = ∀ a → s .IdS (f a) (g a)
  IdS-Π ⦃ s ⦄ .IdS₀ _ = s .IdS₀
  IdS-Π {A = A} {B = B} ⦃ s ⦄ .has-is-ids f = is-identity-system←Sing-sing _ _
    (singleton←equiv-to-singleton (Σ-Π-swap≃ B (λ x bx → s .IdS (f _) bx) )
      (weak-funext (λ a → SingS-is-single s (f a)))) 
    

{-# OVERLAPPABLE IdS-Π #-}

-- instance
--   IdS-Πi : ∀ {𝓤 𝓥 𝓦} {A : Type 𝓤} {B : A → Type 𝓥}
--           → ⦃ _ : ∀ {a} → Identity-system (B a) 𝓦 ⦄
--           → Identity-system ({a : A} → B a) (𝓤 ⊔ 𝓦)
--   IdS-Πi ⦃ s ⦄ .IdS f g = ∀ {a} → s .IdS (f {a}) g 
--   IdS-Πi ⦃ s ⦄ .IdS₀ = s .IdS₀
--   IdS-Πi {A = A} {B} ⦃ s ⦄ .has-is-ids f = is-identity-system←Sing-sing _ _
--          {!!}


instance
  IdS-uncurry
    : ∀ {𝓤 𝓥 𝓦 𝓛} {A : Type 𝓤} {B : A → Type 𝓥} {C : (x : A) → B x → Type 𝓦}
    → ⦃ sb : Identity-system ((x : A) (y : B x) → C x y) 𝓛 ⦄
    → Identity-system ((p : Σ A B) → C (p .fst) (p .snd)) 𝓛
  IdS-uncurry ⦃ s ⦄ .IdS f g =  s .IdS (curry f) (curry g)
  IdS-uncurry ⦃ s ⦄ .IdS₀ = s .IdS₀
  IdS-uncurry {A = A} {B} {C} ⦃ s ⦄ .has-is-ids f = is-identity-system←Sing-sing _ _
    (singleton←equiv-to-singleton (Σ-ap-≃-fst uncurry≃) (SingS-is-single s (curry f)) )
   
ext! : ∀ {𝓤 𝓥} {A : Type 𝓤} {x y : A} ⦃ s : Identity-system A 𝓥 ⦄
     → s .IdS x y → x ＝ y
ext! ⦃ s ⦄ = Id←IdS s 


IdS←Embedding
  : ∀ {𝓤 𝓥 𝓦} {A : Type 𝓤} {B : Type 𝓥}
  → {f : A → B} → is-prop-map f
  → Identity-system B 𝓦
  → Identity-system A 𝓦
IdS←Embedding {f = f} pm s .IdS a b = s .IdS (f a) (f b)
IdS←Embedding pm s .IdS₀ = s .IdS₀
IdS←Embedding {f = f} pm s .has-is-ids a = is-identity-system←Sing-sing _ _
  (mk-contr (a , IdS₀ s) (is-ss (a , IdS₀ s))) where
   is-ss : is-subsingleton (Σ[ z ∶ _ ] IdS s (f a) (f z))
   is-ss = subsingleton←equiv-to-subsingleton (Σ-ap-≃ (λ z → sym≃ ∙≃ Id≃IdS s)) (pm (f a))

IdS←Equiv
  : ∀ {𝓤 𝓥 𝓦} {A : Type 𝓤} {B : Type 𝓥}
    → (A ≃ B)
    → Identity-system A 𝓦
    → Identity-system B 𝓦
IdS←Equiv eq s = IdS←Embedding (is-prop-map←is-contr-map
                    (is-contr-map←is-equiv ((eq e⁻¹) ._≃_.has-is-eqv))) s    


IdS←Subtype : ∀ {𝓤 𝓥 𝓦} {A : Type 𝓤} {B : A → Type 𝓥}
             → is-subtype B
             → Identity-system A 𝓦
             → Identity-system (Σ A B) 𝓦
IdS←Subtype p s = IdS←Embedding {f = fst} (Σ̃-π-emb (mk-subtype p)) s

instance
  IdS-equiv : ∀ {𝓤 𝓥 𝓦} {A : Type 𝓤} {B : Type 𝓥}
              → {B : Type 𝓦}
              → ⦃ _ : Identity-system (A → B) 𝓥 ⦄
              → Identity-system (A ≃ B) 𝓥
  IdS-equiv ⦃ s ⦄ = IdS←Equiv (≃-rep e⁻¹) (IdS←Subtype (λ _ → is-equiv-is-prop) s)

private module test {𝓤 𝓥 𝓦} {A : Type 𝓤} {B : Type 𝓥} {C : Type 𝓦} where
  _ : {f g : A → B} → f ~ g → f ＝ g
  _ = ext!

  _ : {f g : A × B → C} → ((a : A) (b : B) → f (a , b) ＝ g (a , b)) → f ＝ g
  _ = ext!

  _ : {P : A → Type 𝓦} {f g : Σ A P → B} → ((a : A) (b : P a) → f (a , b) ＝ g (a , b)) → f ＝ g
  _ = ext!
