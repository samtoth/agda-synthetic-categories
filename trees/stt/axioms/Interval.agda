module axioms.Interval where

open import foundations.Prelude

postulate
  I : Type
  i0 i1 : I
  -- iJ : ∀ {𝓤} {A : Type 𝓤} {x : A
  PathP : ∀ {𝓤} (A : I → Type 𝓤)
            (a : A i0) (b : A i1) → Type 𝓤
  toPath : ∀ {𝓤} {A : I → Type 𝓤} → (f : (i : I) → A i) → PathP A (f i0) (f i1)


Path : ∀ {𝓤} (A : Type 𝓤) → (a b : A) → Type 𝓤
Path A = PathP (λ _ → A)

reflP : ∀ {𝓤} {A : Type 𝓤} → {a : A} → Path A a a
reflP {a = a} = toPath λ _ → a

postulate 
  IJ : ∀ {𝓤 𝓥} {A : Type 𝓤} {a : A} (M : ∀ {b} (p : Path A a b) → Type 𝓥)
     → (Mrfl : M {a} reflP) → ∀ {b} (p : Path A a b) → M p

  IJ-β : ∀ {𝓤 𝓥} {A : Type 𝓤} {a : A} (M : ∀ {b} (p : Path A a b) → Type 𝓥)
         → {Mrfl : M {a} reflP} → IJ M Mrfl reflP ＝ Mrfl

  _$_ : ∀ {𝓤} {A : I → Type 𝓤} {a : A i0} {b : A i1} → PathP A a b → (i : I) → A i
  _$i0 : ∀ {𝓤} {A : I → Type 𝓤} {a : A i0} {b : A i1} → (p : PathP A a b) → p $ i0 ＝ a
  _$i1 :  ∀ {𝓤} {A : I → Type 𝓤} {a : A i0} {b : A i1} → (p : PathP A a b) → p $ i1 ＝ b
  toPath-β : ∀ {𝓤} {A : I → Type 𝓤} {p : Π I A} → ∀ i → ((toPath p) $ i) ＝ p i
  
{-# REWRITE _$i0 _$i1 toPath-β #-}

postulate
  toPath-η : ∀ {𝓤} {A : I → Type 𝓤} {a : A i0} {b : A i1} {p : PathP A a b} → toPath (λ i → p $ i) ＝ p

{-# REWRITE toPath-η #-}

fromPath : ∀ {𝓤} {A : Type 𝓤} {a b : A} → Path A a b → a ＝ b
fromPath {a = a} = IJ (λ {v} p → a ＝ v) refl

path-drop-j : ∀ {𝓤} {A : I → Type 𝓤} → (p : (i : I) → A i) → PathP (λ i → p i ＝ p i) refl refl
path-drop-j p = toPath (λ i → refl {a = p i})
