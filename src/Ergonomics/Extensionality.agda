module Ergonomics.Extensionality where

open import Foundations.Prelude
open import Foundations.IdentitySystem public
open import Foundations.Subtypes
open import Foundations.EquivContrFibre

open import ufAxioms
open Identity-system ⦃ ... ⦄ public
module Reasoning {𝓤 𝓥} {A : Type 𝓤} ⦃ S : Identity-system A 𝓥 ⦄ where
  open IdSReasoning S public

open Reasoning public

instance
  IdS-default : ∀ {𝓤} {A : Type 𝓤} → Identity-system A 𝓤
  IdS-default .IdS = _＝_
  IdS-default .IdS←Id = id
  IdS-default .has-is-ids a _ = id-is-equiv

{-# INCOHERENT IdS-default #-}

instance
  IdS-Π : ∀ {𝓤 𝓥 𝓦} {A : Type 𝓤} {B : A → Type 𝓥}
          → ⦃ _ : ∀ {a} → Identity-system (B a) 𝓦 ⦄
          → Identity-system ((a : A) → B a) (𝓤 ⊔ 𝓦)
  IdS-Π ⦃ s ⦄ .IdS f g = ∀ a → s .IdS (f a) (g a)
  IdS-Π ⦃ s ⦄ .IdS←Id p a = IdS←Id (happly p a)
  IdS-Π {A = A} {B = B} ⦃ s ⦄ .has-is-ids f
    = fundamental-Id _
        ((is-single←equiv-to-single (Σ-Π-swap≃ B (λ x bx → s .IdS (f _) bx) )
                                    (weak-funext (λ a → SingS-is-single (f a)
                                    )))) _

{-# OVERLAPPABLE IdS-Π #-}

instance
  IdS-Πi : ∀ {𝓤 𝓥 𝓦} {A : Type 𝓤} {B : A → Type 𝓥}
          → ⦃ _ : ∀ {a} → Identity-system (B a) 𝓦 ⦄
          → Identity-system ({a : A} → B a) (𝓤 ⊔ 𝓦)
  IdS-Πi ⦃ s ⦄ .IdS f g = ∀ {a} → s .IdS (f {a}) g
  IdS-Πi ⦃ s ⦄ .IdS←Id p = IdS←Id ⦃ s ⦄ (happlyᵢ p)
  IdS-Πi {A = A} {B} ⦃ s ⦄ .has-is-ids f
    = fundamental-Id _
         (is-single←equiv-to-single (Σ-Π-swapᵢ≃ {P = IdS ⦃ s ⦄ f})
           (is-singleton-Πᵢ (SingS-is-single f))) _

_＝ₑ_ : ∀ {𝓤 : Level} {A : Type 𝓤} {𝓥 : Level}
          ⦃ r : Identity-system A 𝓥 ⦄
        → A → A → Type 𝓥
_＝ₑ_ = IdS

instance
  IdS-uncurry
    : ∀ {𝓤 𝓥 𝓦 𝓛} {A : Type 𝓤} {B : A → Type 𝓥} {C : (x : A) → B x → Type 𝓦}
    → ⦃ sb : Identity-system ((x : A) (y : B x) → C x y) 𝓛 ⦄
    → Identity-system ((p : Σ A B) → C (p .fst) (p .snd)) 𝓛
  IdS-uncurry ⦃ s ⦄ .IdS f g =  s .IdS (curry f) (curry g)
  IdS-uncurry ⦃ s ⦄ .IdS←Id refl = IdS←Id ⦃ s ⦄ refl
  IdS-uncurry {A = A} {B} {C} ⦃ s ⦄ .has-is-ids f
    = fundamental-Id _
      (is-single←equiv-to-single (Σ-ap-≃-fst uncurry≃)
                                 (SingS-is-single ⦃ s ⦄ (curry f))) _

ext! : ∀ {𝓤 𝓥} {A : Type 𝓤} ⦃ s : Identity-system A 𝓥 ⦄ {x y : A}
     → s .IdS x y → x ＝ y
ext! = Id←IdS

ext!-is-equiv : ∀ {𝓤 𝓥} {A : Type 𝓤} {x y : A}
                  ⦃ s : Identity-system A 𝓥 ⦄
                → is-equiv (ext! ⦃ s ⦄ {x} {y})
ext!-is-equiv = is-equiv⁻¹ (has-is-ids _ _)


ext!≃ :  ∀ {𝓤 𝓥} {A : Type 𝓤} {x y : A} ⦃ s : Identity-system A 𝓥 ⦄
     → Id A x y ≃ IdS x y
ext!≃ = Id≃IdS

ext!≃' :  ∀ {𝓤 𝓥} {A : Type 𝓤} {x y : A} ⦃ s : Identity-system A 𝓥 ⦄
     → IdS x y ≃ Id A x y
ext!≃' ⦃ s ⦄ = Id≃IdS e⁻¹

IdS←Embedding
  : ∀ {𝓤 𝓥 𝓦} {A : Type 𝓤} {B : Type 𝓥}
  → {f : A → B} → is-prop-map f
  → Identity-system B 𝓦
  → Identity-system A 𝓦
IdS←Embedding {f = f} pm s .IdS a b = IdS ⦃ s ⦄ (f a) (f b)
IdS←Embedding pm s .IdS←Id refl = IdS←Id ⦃ s ⦄ refl
IdS←Embedding {f = f} pm s .has-is-ids a
  = fundamental-Id _
                   ((mk-singl (a , IdS₀ ⦃ s ⦄) (is-ss (a , IdS₀ ⦃ s ⦄))))
                   _
   where
   is-ss : is-prop (Σ[ z ∶ _ ] IdS ⦃ s ⦄ (f a) (f z))
   is-ss = is-prop←equiv-to-prop (Σ-ap-≃ (λ z → sym≃ ∙≃ Id≃IdS ⦃ s ⦄)) (pm (f a))

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
IdS←Subtype p s = IdS←Embedding {f = fst} Σ̃-π-is-prop-map s
  where open Subtype (mk-subtype p)

instance
  IdS-equiv : ∀ {𝓤 𝓥 𝓦} {A : Type 𝓤} {B : Type 𝓥}
              → ⦃ _ : Identity-system (A → B) 𝓦 ⦄
              → Identity-system (A ≃ B) 𝓦
  IdS-equiv ⦃ s ⦄ = IdS←Equiv (≃-rep e⁻¹) (IdS←Subtype (λ _ → is-equiv-is-prop) s)

private module test {𝓤 𝓥 𝓦} {A : Type 𝓤} {B : Type 𝓥} {C : Type 𝓦} where
  _ : {f g : A → B} → f ~ g → f ＝ g
  _ = ext!

  _ : {f g : A × B → C} → ((a : A) (b : B) → f (a , b) ＝ g (a , b)) → f ＝ g
  _ = ext!

  _ : {P : A → Type 𝓦} {f g : Σ A P → B} → ((a : A) (b : P a) → f (a , b) ＝ g (a , b)) → f ＝ g
  _ = ext!

instance
  IdS-Sigma : ∀ {𝓤 𝓥 𝓦 𝓜} {A : Type 𝓤} {B : A → Type 𝓥}
              → ⦃ _ : Identity-system A 𝓦 ⦄
              → ⦃ _ : ∀ {a : A} → Identity-system (B a) 𝓜 ⦄
              → Identity-system (Σ A B) (𝓦 ⊔ 𝓜)
  IdS-Sigma ⦃ A ⦄ ⦃ B ⦄ .IdS (a , b) (a' , b')
    = Σ[ p ∶ IdS a a' ] IdS (trS ⦃ A ⦄ p b) b'
  IdS-Sigma ⦃ A ⦄ ⦃ B ⦄ .IdS←Id {(a , b)} refl = IdS₀ ⦃ A ⦄ , IdS₀ ⦃ B ⦄
  IdS-Sigma {A = A}{B}⦃ As ⦄ ⦃ Bs ⦄ .has-is-ids (a , b)
    = fundamental-Id _
      (is-single←equiv-to-single (lem e⁻¹) (SingS-is-single ⦃ Bs ⦄ b)) _ where
    lem : Σ (Σ A B) (λ where (a' , b') → Σ[ p ∶ IdS a a' ] IdS (trS ⦃ As ⦄ p b) b')
           ≃
          SingS ⦃ Bs ⦄ b
    lem =
         Σ (Σ A B)
           (λ { (a' , b')
                  → Σ[ p ∶ IdS a a' ]
                     IdS (trS ⦃ As ⦄ p b) b'
              })

             ≃⟨ Σ-assoc ⟩

          (Σ[ a' ∶ A ] Σ[ b' ∶ B a' ]
            Σ[ p ∶ IdS a a' ] IdS (trS ⦃ As ⦄ p b) b')

            ≃⟨ Σ-ap-≃ (λ a₁ → Σ-comm) ⟩

          (Σ[ a' ∶ A ]  Σ[ p ∶ IdS a a' ]
            Σ[ b' ∶ B a' ] IdS (trS ⦃ As ⦄ p b) b')

            ≃⟨ Σ-singS' ⦃ As ⦄ ⟩

          SingS ⦃ Bs ⦄ b ≃∎

{-# OVERLAPPABLE IdS-Sigma #-}


instance
  IdS-ua : ∀ {𝓤} → Identity-system (Type 𝓤) 𝓤
  IdS-ua = mk-identity-system _≃_ ua≃
