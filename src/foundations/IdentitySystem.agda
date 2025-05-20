module foundations.IdentitySystem where

open import foundations.Universes
open import foundations.Sigma
open import foundations.CurryEquiv
open import foundations.SigmaPath
open import foundations.SigmaProperties
open import foundations.FibrewiseEquiv
open import foundations.Identity
open import foundations.DependentIdentity
open import foundations.Functions
open import foundations.FunctionInverses
open import foundations.Singleton
open import foundations.SingletonClosure
open import foundations.CoherentIsomorphism
open import foundations.QuasiIsomorphism
open import foundations.EquivContrFibre
open import foundations.EquivHomotopy
open import foundations.EquivSingleton

module _ {𝓤} (A : Type 𝓤) (a₀ : A) where
  Reflexive-ppred : ∀ 𝓥 → Type _
  Reflexive-ppred 𝓥 = Σ[ R ∶ (A → Type 𝓥) ] R a₀

  SingR : ∀ {𝓥} (R : A → A → Type 𝓥) → Type (𝓤 ⊔ 𝓥)
  SingR R = Σ[ b ∶ A ] R a₀ b

idtoppred : ∀ {𝓤 𝓥} {A : Type 𝓤} {a : A} → (R : Reflexive-ppred A a 𝓥)
            → ∀ b → (a ＝ b) → R .fst b
idtoppred (R , R₀) _ p = tr _ p R₀

is-identity-system-at : ∀ {𝓤 𝓥} → (A : Type 𝓤) → (a₀ : A)
                      → Reflexive-ppred A a₀ 𝓥
                      → Type _
is-identity-system-at A a₀ (R , R₀) = is-fibrewise-equiv (idtoppred (R , R₀))


record Identity-system {𝓤} (A : Type 𝓤) 𝓥 : Type (𝓤 ⊔ lsuc 𝓥) where
  field
    IdS  : A → A → Type 𝓥
    IdS₀ : ∀ {a} → IdS a a

  Rpp : ∀ a → Reflexive-ppred A a 𝓥
  Rpp a = (IdS a , IdS₀)

  field
    has-is-ids : ∀ a → is-identity-system-at A a (Rpp a)

  module ids-eqv {a b} = is-equiv (has-is-ids a b)

  IdS←Id : ∀ {a b} → a ＝ b → IdS a b
  IdS←Id = idtoppred (Rpp _) _

  open ids-eqv public renaming
    (bwd to Id←IdS
    ; ε to IdS←Id←IdS
    ; η to Id←IdS←Id) using ()

module IdSReasoning {𝓤 𝓥} {A : Type 𝓤} (Id : Identity-system A 𝓥) where
  open Identity-system Id

  SingS : A → Type _
  SingS a = SingR A a IdS

  tr←idtopred : ∀ {a b : A} → (p : a ＝ b) → tr _ p (IdS₀ {a}) ＝ idtoppred (Rpp a) b p
  tr←idtopred refl = refl

  SingS-is-single : ∀ a → is-singleton (SingS a)
  SingS-is-single a = mk-singl (a , IdS₀) I where
    I : (x : SingS a) → (a , IdS₀) ＝ x
    I (b , p) = Σ-path→ (Id←IdS p , tr←idtopred (Id←IdS p) ∙ IdS←Id←IdS p)

  Id≃IdS : ∀ {a b} → (a ＝ b) ≃ IdS a b
  Id≃IdS = (mk≃ IdS←Id (has-is-ids _ _))

  -- IdS≃Id : ∀ {a b} → IdS a b ≃ (a ＝ b)
  -- IdS≃Id = Id←IdS , {!has-is-ids _ _!}

  opaque
    IdSJ : ∀ {𝓦} {a} (P : SingS a → Type 𝓦)
         → (P₀ : P (a , IdS₀)) → ∀ {b} (p : IdS a b)
         → P (_ , p)
    IdSJ P p₀ p = tr id
                   (ap P (SingS-is-single _ .central (_ , p)))
                   p₀


    IdSJ-refl : ∀ {𝓦} {a} (P : SingS a → Type 𝓦)
              → {P₀ : P (a , IdS₀)}
              → IdSJ P P₀ IdS₀ ＝ P₀
    IdSJ-refl {a = a} P {P₀}
      = IdSJ P P₀ IdS₀                              ＝⟨⟩
        tr id (ap P (SingS-is-single _ .central _)) P₀ ＝⟨ ap (λ p → tr id (ap P p) P₀) lem ⟩
        tr id (ap P refl) P₀                  ＝⟨⟩
        P₀ ∎  where

      lem : SingS-is-single a .central (_ , IdS₀) ＝ refl
      lem = is-prop←is-single (Singleton-Id (SingS-is-single a) _ _) _ _

  {-# REWRITE IdSJ-refl #-}

  trS : ∀ {𝓦} {B : A → Type 𝓦} {a b : A} (p : IdS a b) → B a → B b
  trS {_}{B} p ba = IdSJ (B ∘ fst) ba p

  Σ-singS : ∀ {𝓦} {a' : A} {B : (a : A) → IdS a a' → Type 𝓦}
        → Σ A (λ a → Σ (IdS a a') λ p → B a p) ≃ B a' IdS₀
  Σ-singS {_} {a'}{B} = iso ∙≃ Σ-＝singl where
    iso : Σ A (λ a → Σ (IdS a a') (B a))
            ≃
         (Σ[ a ∶ A ] Σ[ p ∶ (a ＝ a') ] B a (IdS←Id p))
    iso = Σ-ap-≃ (λ a → Σ-ap-≃-fst Id≃IdS e⁻¹)

  Σ-singS' : ∀ {𝓦} {a' : A} {B : (a : A) → IdS a' a → Type 𝓦}
           → Σ A (λ a → Σ (IdS a' a) λ p → B a p) ≃ B a' IdS₀
  Σ-singS' {_} {a'}{B} = iso ∙≃ Σ-＝singl' where
    iso : Σ A (λ a → Σ (IdS a' a) (B a))
            ≃
         (Σ[ a ∶ A ] Σ[ p ∶ (a' ＝ a) ] B a (IdS←Id p))
    iso = Σ-ap-≃ (λ a → Σ-ap-≃-fst Id≃IdS e⁻¹)

-- Reflexive-ppred : ∀ 𝓥 → Type _
-- Reflexive-ppred 𝓥 = Σ[ R ∶ (A → Type 𝓥) ] R a₀

-- SingR : ∀ {𝓥} (R : A → A → Type 𝓥) → Type (𝓤 ⊔ 𝓥)
-- SingR R = Σ[ b ∶ A ] R a₀ b

is-identity-system←Sing-sing : ∀ {𝓤 𝓥} {A : Type 𝓤} {a₀}
                                → (R : A → Type 𝓥)
                                → (R₀ : R a₀)
                                → is-singleton (Σ[ b ∶ A ] R b)
                                → is-identity-system-at A a₀ (R , R₀)
is-identity-system←Sing-sing R R₀ Sing-sing b
  = is-equiv←qiso the-iso where
    Sing-recentre : ∀ (p : Σ _ R) → (_ , R₀) ＝ p
    Sing-recentre p = is-prop←is-single Sing-sing _ _

    coh : ∀ {𝓤 𝓥} {A : Type 𝓤} {R : A → Type 𝓥} {x y : Σ A R} (p : x ＝ y) →  ap R (Σ-path-fst p) ＝ ap (λ a → R (fst a)) p
    coh refl = refl

    the-iso : quasi-iso (idtoppred (R , R₀) b)
    the-iso .fst rb = Σ-path-fst (Sing-recentre (_ , rb))
    the-iso .snd .fst refl = ap Σ-path-fst (is-prop←is-single
                                            (Singleton-Id Sing-sing _ _)
                                             _ _)
    the-iso .snd .snd rb =    happly (ap coe (coh (Sing-recentre (_ , rb)))) R₀ ∙ Σ-path-snd (Sing-recentre (_ , rb))


-- TODO: Find special place for this
--    creds to Egbert/agda-unimath
--  The idea is that we have some type of the form Σ A ...,
--   given a basepoint (a₀,b₀), the partially applied equality type
--   ('SingR') will have the structure, Σ( (a₁,b₁) : Σ A B) Σ (R a₀ a₁) ....
--   It's clear then, that if Σ A (R a₀) is singleton and recursively
--   if Σ b (R b₀) is a singleton, then the whole thing is. And this is pretty
--   handy for defining identity system instances
is-singleton-structure←parts : ∀ {𝓤 𝓥 𝓦 𝓜}{A : Type 𝓤} {B : A → Type 𝓥}
                   {Ra : A → Type 𝓦} {Rb : (a : A) → B a → Ra a → Type 𝓜}
                 → is-singleton (Σ A Ra)
                 → (t@(a , c) : Σ A Ra)
                 → is-singleton (Σ[ b ∶ B a ] Rb a b c)
                 → is-singleton (Σ[ t@(a , b) ∶ (Σ A B)] Σ (Ra a) (Rb a b))
is-singleton-structure←parts aR t@(a , c) bR
  = is-single←equiv-to-single Σ-interchange (Singleton-Σ' aR t bR)


family~idtoppred  : ∀ {𝓤 𝓥} {A : Type 𝓤} {B : A → Type 𝓥} {a₀ : A} (f : (a : A) → (a₀ ＝ a) → B a)
             → {a : A} → (p : a₀ ＝ a) → (idtoppred (B , f a₀ refl) a) p ＝ f a p
family~idtoppred f refl = refl


family-equiv←Sing-sing : ∀ {𝓤 𝓥} {A : Type 𝓤} {B : A → Type 𝓥} {a₀ : A}
                       → (f : (a : A) → (a₀ ＝ a) → B a)
                       → is-singleton (Σ[ a ∶ A ] B a)
                       → (a : A) → is-equiv (f a)
family-equiv←Sing-sing {B = B} {a₀} f H a = homotopy-is-equiv (family~idtoppred f) (is-identity-system←Sing-sing B (f a₀ refl) H a )

ap-equiv←equiv : ∀ {𝓤 𝓥} {A : Type 𝓤} {B : Type 𝓥} {f : A → B} {x y : A} →
               is-equiv f → is-equiv (ap  f)
ap-equiv←equiv {A = A} {f = f} {x} {y} h = family-equiv←Sing-sing (λ a → ap f) sing y where
  sing : is-singleton (Σ A (λ z → f x ＝ f z))
  sing = is-single←section-single (total-map (λ a → sym))
                                  ((λ (a , p) → (a , (sym p))) , λ x →  Σ-path→ (refl , sym-sym))
                                  (is-contr-map←is-equiv h (f x))
