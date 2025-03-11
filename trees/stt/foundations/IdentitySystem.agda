module foundations.IdentitySystem where

open import foundations.universe
open import foundations.Sigma
open import foundations.SigmaPath
open import foundations.Identity
open import foundations.DependentIdentity
open import foundations.Functions
open import foundations.FunctionInverses
open import foundations.Singleton
open import foundations.SingletonClosure
open import foundations.CoherentIsomorphism

module _ {𝓤} (A : Type 𝓤) (a₀ : A) where
  Reflexive-ppred : ∀ 𝓥 → Type _
  Reflexive-ppred 𝓥 = Σ[ R ∶ (A → Type 𝓥) ] R a₀


idtoppred : ∀ {𝓤 𝓥} {A : Type 𝓤} {a : A} → (R : Reflexive-ppred A a 𝓥) → ∀ b → (a ＝ b) → R .fst b
idtoppred (R , R₀) _ refl = R₀

is-identity-system-at : ∀ {𝓤 𝓥} → (A : Type 𝓤) → (a₀ : A)
                      → Reflexive-ppred A a₀ 𝓥
                      → Type _
is-identity-system-at A a₀ (R , R₀) = ∀ b → is-equiv (idtoppred (R , R₀) b)


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

  open ids-eqv public renaming (bwd to Id←IdS ; ε to IdS←Id←IdS ; η to Id←IdS←Id) using ()

module _ {𝓤 𝓥} {A : Type 𝓤} (Id : Identity-system A 𝓥) where
  open Identity-system Id

  tr←idtopred : ∀ {a b : A} → (p : a ＝ b) → tr p (IdS₀ {a}) ＝ idtoppred (Rpp a) b p 
  tr←idtopred refl = refl

  SingS : A → Type _
  SingS a = Σ[ b ∶ A ] IdS a b 

  SingS-is-single : ∀ a → is-singleton (SingS a)
  SingS-is-single a = mk-contr (a , IdS₀) I where 
    I : (x : SingS a) → (a , IdS₀) ＝ x
    I (b , p) = Σ-path→ (Id←IdS p , tr←idtopred (Id←IdS p) ∙ IdS←Id←IdS p)

  opaque 
    IdSJ : ∀ {𝓦} {a} (P : SingS a → Type 𝓦)
         → (P₀ : P (a , IdS₀)) → ∀ {b} (p : IdS a b)
         → P (_ , p)
    IdSJ P p₀ p = tr {P = λ x → x}
                   (ap P (SingS-is-single _ .central (_ , p)))
                   p₀


    IdSJ-refl : ∀ {𝓦} {a} (P : SingS a → Type 𝓦)
              → {P₀ : P (a , IdS₀)}
              → IdSJ P P₀ IdS₀ ＝ P₀
    IdSJ-refl {a = a} P {P₀}
      = IdSJ P P₀ IdS₀                             ＝⟨⟩
        tr (ap P (SingS-is-single _ .central _)) P₀ ＝⟨ ap (λ p → tr {P = id} (ap P p) P₀) lem ⟩
        tr {P = id} (ap P refl) P₀                 ＝⟨⟩
        P₀ ∎  where

      lem : SingS-is-single a .central (_ , IdS₀) ＝ refl
      lem = is-prop←is-single (Singleton-Id (SingS-is-single a) _ _) _ _

  {-# REWRITE IdSJ-refl #-}
    
