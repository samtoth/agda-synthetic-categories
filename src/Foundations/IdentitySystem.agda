module Foundations.IdentitySystem where

open import Foundations.Universes
open import Foundations.Sigma
open import Foundations.PiProperties
open import Foundations.SigmaPath
open import Foundations.SigmaProperties
open import Foundations.FibrewiseEquiv
open import Foundations.Identity
open import Foundations.DependentIdentity
open import Foundations.Functions
open import Foundations.FunctionInverses
open import Foundations.Homotopy
open import Foundations.Singleton
open import Foundations.SingletonClosure
open import Foundations.CoherentIsomorphism
open import Foundations.QuasiIsomorphism
open import Foundations.TotalEquiv
open import Foundations.EquivOfSingleton
open import Foundations.EquivContrFibre
open import Foundations.EquivHomotopy
open import Foundations.EquivSingleton

module _ {𝓤} (A : Type 𝓤) (a₀ : A) where
  Reflexive-ppred : ∀ 𝓥 → Type _
  Reflexive-ppred 𝓥 = Σ[ R ∶ (A → Type 𝓥) ] R a₀

  SingR : ∀ {𝓥} (R : A → A → Type 𝓥) → Type (𝓤 ⊔ 𝓥)
  SingR R = Σ[ b ∶ A ] R a₀ b

  SingR' : ∀ {𝓥} (R : A → A → Type 𝓥) → Type (𝓤 ⊔ 𝓥)
  SingR' R = Σ[ b ∶ A ] R b a₀


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
    IdS←Id : ∀ {a b} → a ＝ b → IdS a b

  IdS₀ : ∀ {a} → IdS a a
  IdS₀ = IdS←Id refl

  Rpp : ∀ a → Reflexive-ppred A a 𝓥
  Rpp a = (IdS a , IdS₀)

  field
    has-is-ids : ∀ a b → is-equiv (IdS←Id {a} {b})

  module ids-eqv {a b} = is-equiv (has-is-ids a b)

  open ids-eqv public renaming
    (bwd to Id←IdS
    ; ε to IdS←Id←IdS
    ; η to Id←IdS←Id) using ()

mk-identity-system : ∀ {𝓤 𝓥} {A : Type 𝓤} → (I : A → A → Type 𝓥)
                     → (∀ {x y} → I x y ≃ (x ＝ y))
                     → Identity-system A 𝓥
mk-identity-system I eq = ids where
  module eq {x y} = _≃_ (eq {x} {y})

  ids : Identity-system _ _
  ids .Identity-system.IdS = I
  ids .Identity-system.IdS←Id = eq.bwd
  ids .Identity-system.has-is-ids x y = is-equiv⁻¹ eq.has-is-eqv


module IdSReasoning {𝓤 𝓥} {A : Type 𝓤} (Id : Identity-system A 𝓥) where
  open Identity-system Id

  SingS : A → Type _
  SingS a = SingR A a IdS

  SingS' : A → Type _
  SingS' a = SingR' A a IdS

  tr←idtopred : ∀ {a b : A} → (p : a ＝ b) → tr _ p (IdS₀ {a}) ＝ IdS←Id p
  tr←idtopred refl = refl

  tr←idtopred' : ∀ {a b : A} → (p : a ＝ b) → tr (λ x → IdS x b) (sym p) (IdS₀ {b}) ＝ IdS←Id p
  tr←idtopred' refl = refl

  SingS-is-single : ∀ a → is-singleton (SingS a)
  SingS-is-single a = mk-singl (a , IdS₀) I where
    I : (x : SingS a) → (a , IdS₀) ＝ x
    I (b , p) = Σ-path→ (Id←IdS p , tr←idtopred (Id←IdS p) ∙ IdS←Id←IdS p)

  SingS-is-single' : ∀ a → is-singleton (SingS' a)
  SingS-is-single' a = mk-singl (a , IdS₀) I where
    I : (x : SingS' a) → (a , IdS₀) ＝ x
    I (b , p) = Σ-path→ (sym (Id←IdS p) , tr←idtopred' (Id←IdS p) ∙ IdS←Id←IdS p)

  Id≃IdS : ∀ {a b} → (a ＝ b) ≃ IdS a b
  Id≃IdS = (mk≃ IdS←Id (has-is-ids _ _))

  IdS≃Id : ∀ {a b} → IdS a b ≃ (a ＝ b)
  IdS≃Id = mk≃ Id←IdS (is-equiv⁻¹ (has-is-ids _ _))

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
  Σ-singS {_} {a'}{B} = Σ-assoc e⁻¹ ∙≃ Σ-singl (SingS-is-single' a') (a' , IdS₀)

  Σ-singS' : ∀ {𝓦} {a' : A} {B : (a : A) → IdS a' a → Type 𝓦}
           → Σ A (λ a → Σ (IdS a' a) λ p → B a p) ≃ B a' IdS₀
  Σ-singS' {_} {a'}{B} = Σ-assoc e⁻¹ ∙≃ Σ-singl (SingS-is-single a') (a' , IdS₀)


-- fundamental theorem of Identity types
fundamental-Id : ∀ {𝓤 𝓥} {A : Type 𝓤} {a₀}
                                → (R : A → Type 𝓥)
                                → is-singleton (Σ[ b ∶ A ] R b)
                                → (f : ∀ b → a₀ ＝ b → R b)
                                → is-fibrewise-equiv f
fundamental-Id {a₀ = a₀} R Sing-sing f
  = is-fibrewise-equiv←is-total-equiv
             (is-equiv←single-to-prop Sing-is-singleton
                                      (is-prop←is-single Sing-sing)
                                      (total-map f))

remove-singleton-structure
  : ∀ {𝓤 𝓥 𝓦} {A : Type 𝓤} {B : A → Type 𝓥}
      {Ra : A → Type 𝓦}
    → is-singleton  (Σ A Ra)
    → ((a , _) : Σ A Ra)
    → (Σ[ (a , b) ∶ Σ A B ] Ra a) ≃ B a
remove-singleton-structure ars a
  = Σ-assoc
  ∙≃ Σ-ap-≃ (λ _ → ×-swap)
  ∙≃ Σ-assoc e⁻¹
  ∙≃ Σ-singl ars a

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


ap-equiv←equiv : ∀ {𝓤 𝓥} {A : Type 𝓤} {B : Type 𝓥} {f : A → B} {x y : A} →
               is-equiv f → is-equiv (ap  f)
ap-equiv←equiv {A = A} {f = f} {x} {y} h = fundamental-Id _ sing (λ a → ap f) y where abstract
  sing : is-singleton (Σ A (λ z → f x ＝ f z))
  sing = is-single←section-single (total-map (λ a → sym))
                                  ((λ (a , p) → (a , (sym p))) , λ x →  Σ-path→ (refl , sym-sym))
                                  (is-contr-map←is-equiv h (f x))
