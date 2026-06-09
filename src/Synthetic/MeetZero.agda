open import Foundations.Universes
open import Foundations.Nat
open import Foundations.Unit

open import Algebra.Lattice

open import Synthetic.Tiny

open import Modalities.Cohesion.Connectivity
open import Modalities.Cohesion.Continuity

import Synthetic.Cubes



module Synthetic.MeetZero
  {@♭ 𝓘} (@♭ Δ¹ : Type 𝓘) (@♭ I : Lattice Δ¹) (@♭ I-distr : is-distributive I)
  (open Lattice I renaming (0l to i0; 1l to i1))
  (open Synthetic.Cubes Δ¹ i0 i1)
  (@♭ cubes-detect-cont : detects-continuity {I = ℕ} □^_)
  (@♭ ♭Δ¹-ind : ∀ {𝓤} (P : @♭ Δ¹ → Type 𝓤) → P i0 → P i1 → (@♭ x : Δ¹) → P x)
  (@♭ is-directed : ∀ (f : Δ¹ → Δ¹) i j → i ≤ j → f i ≤ f j)
  where


open import Axioms.UF

open import Foundations.Prelude

open import Modalities.Subuniverses
open import Modalities.GlobalSubuniverses
open import Modalities.GlobalReflectiveSubuniverses
open import Modalities.Instances.Localisation
open import Modalities.Instances.Nullification
open import Modalities.Instances.Truncation

open import Modalities.Cohesion.Flat
open import Modalities.Cohesion.FlatLex
open import Modalities.Cohesion.LiftingSquares

open import Ergonomics.Auto
open import Ergonomics.Extensionality

open import Core.Arrows
open import Core.ArrowEquiv
open import Core.PullbackPowers
open import Core.Orthogonal
open import Core.OrthogonalClosure
open import Core.FunctorialityPullbacks
open import Core.GlobalClassesMaps
open import Core.UniversalFibrations

open import Synthetic.Hom Δ¹ i0 i1
open import Synthetic.Boundaries Δ¹ I
open import Synthetic.Categories.CovariantFamilies Δ¹ I
open import Synthetic.Categories.CovariantClosure Δ¹ I

opaque
  cubes-separate : family-separates □^_
  cubes-separate = family-separates←detects-continuity □^_ cubes-detect-cont

  cubes-separate'
    : ∀ {@♭ 𝓤 𝓥} (@♭ fa : Arrow 𝓤 𝓥) (let @♭ f = Arrow.f fa)
      → @♭ ((∀ {@♭ n} → is-equiv (♭-map (postcomp (□^ n) f))))
      → is-equiv f
  cubes-separate' fa eq
    = cubes-separate
        fa
        (tgt-is-equiv←Arrow-equiv (amap , amap-is-equiv) (eq {0}))
        eq where
    open Arrow fa
    amap : Arrow-map (♭-map (postcomp (□^ 0) f)) (♭-map f)
    amap .Arrow-Π.top = ♭-map (ev ttᴸ)
    amap .Arrow-Π.bot = ♭-map (ev ttᴸ)
    amap .Arrow-Π.comm (mod♭ f) = refl

    amap-is-equiv : is-Arrow-equiv amap
    amap-is-equiv .fst = ♭-map-is-equiv (sing-ev-is-equiv global-funext single!)
    amap-is-equiv .snd = ♭-map-is-equiv (sing-ev-is-equiv global-funext single!)


open import Core.Joins

_≤^_ : {n : ℕ} → □^ n → □^ n → Type 𝓘
_≤^_ {zero} _ _ = 𝟙ᴸ
_≤^_ {suc zero} i j = i ≤ j
_≤^_ {suc (suc n)} (i , i') (j , j') = (i ≤^ j) × (i' ≤ j')

module _ (i j : Δ¹) where
  interp1 : (t : Δ¹) → Δ¹
  interp1 t = i ∨ (t ∧ j)

  interp1-0 : i ≤ j → interp1 i0 ＝ i
  interp1-0 _ = ap (i ∨_) 0-init ∙ 0-bottom

  interp1-1 : i ≤ j → interp1 i1 ＝ j
  interp1-1 h = ap (i ∨_) (∧-comm ∙ 1-top) ∙ ≤-max h

interp : {n : ℕ} (i j : □^ n) → (t : Δ¹) → □^ n
interp {zero} i j t = ttᴸ
interp {suc zero} i j t = i ∨ (t ∧ j)
interp {suc (suc n)} (i' , i) (j' , j) t .fst = interp i' j' t
interp {suc (suc n)} (i' , i) (j' , j) t .snd = i ∨ (t ∧ j)

interp-0 : {n : ℕ} (i j : □^ n) (h : i ≤^ j) → interp i j i0 ＝ i
interp-0 {zero} i j h = refl
interp-0 {suc zero} i j h = interp1-0 i j h
interp-0 {suc (suc n)} (i' , i) (j' , j) (h' , h) =
  ×-path→ (interp-0 i' j' h' , interp1-0 i j h)

interp-1 : {n : ℕ} (i j : □^ n) (h : i ≤^ j) → interp i j i1 ＝ j
interp-1 {zero} i j h = refl
interp-1 {suc zero} i j h = interp1-1 i j h
interp-1 {suc (suc n)} (i' , i) (j' , j) (h' , h) =
  ×-path→ (interp-1 i' j' h' , interp1-1 i j h)

module _ {n : ℕ} (f : □^ n → Δ¹) (i j : □^ n) (h : i ≤^ j) where
  help : f (interp i j i0) ≤ f (interp i j i1)
  help = is-directed (f ∘ interp i j) i0 i1 1-top

  mono1 : f i ≤ f j
  mono1 =
    tr (λ x → f x ≤ f j) (interp-0 i j h)
      (tr (λ x → f (interp i j i0) ≤ f x) (interp-1 i j h) help)

mono : {n m : ℕ} (f : □^ n → □^ m) (i j : □^ n) → i ≤^ j → f i ≤^ f j
mono {n} {zero} f i j h = ttᴸ
mono {n} {suc zero} f i j h = mono1 f i j h
mono {n} {suc (suc m)} f i j h = mono (fst ∘ f) i j h , mono1 (snd ∘ f) i j h

□-1-top : {n : ℕ} → {k : □^ n} → k ≤^ □-1
□-1-top {zero} = ttᴸ
□-1-top {suc zero} = 1-top
□-1-top {suc (suc n)} = □-1-top , 1-top

mono' : {n m : ℕ} → (f : □^ n → □^ m) → (P : □^ m → Type 𝓘) →
        (∀ {i j} → i ≤^ j → P j → P i) → P (f □-1) → (k : □^ n) → P (f k)
mono' f P hP hf k = hP (mono f k □-1 □-1-top) hf


P1 : □^ 2 → Type 𝓘
P1 (i , j) = (i ＝ i0) * (j ＝ i0)

is-prop-P1 : {p : □^ 2} → is-prop (P1 p)
is-prop-P1 = *-is-prop (carrier-is-set _ _) (carrier-is-set _ _)

lem1 : {i : Δ¹} → i ≤ i0 → i ＝ i0
lem1 h = sym h ∙ ∧-comm ∙ 0-init

P1-mono : {i j : □^ 2} → i ≤^ j → P1 j → P1 i
P1-mono {i1 , i2} {j1 , j2} (h1 , h2) =
  *-prop-rec is-prop-P1
    (λ H1 → ι₁ (lem1 (tr (i1 ≤_) H1 h1)))
    (λ H2 → ι₂ (lem1 (tr (i2 ≤_) H2 h2)))

P2 : □^ 2 → Type 𝓘
P2 (i , j) = i ∧ j ＝ i0

is-prop-P2 : {p : □^ 2} → is-prop (P2 p)
is-prop-P2 = carrier-is-set _ _

lem : (i j : Δ¹) → P1 (i , j) → P2 (i , j)
lem i j = *-prop-rec (carrier-is-set _ _)
  (λ hi → ap (_∧ j) hi  ∙ 0-init)
  (λ hj → ap (i ∧_) hj ∙ ∧-comm ∙ 0-init)

cmp : Σ (□^ 2) P1 → Σ (□^ 2) P2
cmp x .fst = x .fst
cmp x .snd = lem (x .fst .fst) (x .fst .snd) (x .snd)

vert' : (@♭ i j : Δ¹) → P2 (i , j) → P1 (i , j)
vert' = ♭Δ¹-ind _ (λ _ _ → ι₁ refl)
  (♭Δ¹-ind _ (λ _ → ι₂ refl) (λ h → ι₁ (sym 1-top ∙ h)))

vert : (@♭ ij : □^ 2) → P2 ij → P1 ij
vert (i , j) = vert' i j

vert-f : {@♭ n : ℕ} → (@♭ f : □^ n → □^ 2) → (∀ k → P2 (f k)) → (∀ k → P1 (f k))
vert-f f hf k = mono' f P1 P1-mono (vert (f □-1) (hf □-1)) k

goal3 : {@♭ n : ℕ} → section (♭-map (postcomp (□^ n) cmp))
goal3 .fst (mod♭ f) = mod♭ λ p → f p .fst , vert-f (fst ∘ f) (snd ∘ f) p
goal3 .snd (mod♭ f) = mapply♭ (mod♭ (funext→ (λ p → Σ-path→ (refl , is-prop-P2 _ _))))

♭-map-is-injective
  : ∀ {@♭ 𝓤 𝓥} {@♭ A : Type 𝓤} {@♭ B : Type 𝓥} {@♭ f : A → B}
    → @♭ (∀ {a a'} → f a ＝ f a' → a ＝ a')
    → ∀ {a a'} → ♭-map f a ＝ ♭-map f a' → a ＝ a'
♭-map-is-injective fi {mod♭ a} {mod♭ a'} =
  (λ where (mod♭ b) → mapply♭ (mod♭ (fi b))) ∘ modext♭

goal2 : is-equiv cmp
goal2 = cubes-separate' (mk-arrow cmp)
  (is-equiv←section←injective {f = ♭-map (postcomp (□^ _) cmp)}
   (♭-map-is-injective inj) goal3)
  where
    inj : {@♭ n : ℕ} → {f f' : □^ n → Σ (□^ 2) P1} →
      postcomp (□^ n) cmp f ＝ postcomp (□^ n) cmp f' →
      f ＝ f'
    inj {n} {f} {f'} h =
      funext→ (λ p → Σ-path→ (Σ-path-fst (happly h p) , is-prop-P1 _ _))

goal : (i j : Δ¹) → i ∧ j ＝ i0 → (i ＝ i0) * (j ＝ i0)
goal i j h = tr P1 (happly e' (((i , j) , h))) (bwd goal2 ((i , j) , h) .snd)
  where
    open is-equiv
    e' : fst ∘ bwd goal2 ＝ fst
    e' = ap (fst ∘_) (funext→ (ε goal2))
