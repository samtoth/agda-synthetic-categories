
open import foundations.universe
open import foundations.Identity
open import foundations.Functions

-- equational reasoning for a wild category

module foundations.Reasoning {𝓤} {𝓥} (Ob : Type 𝓤) (Hom : Ob → Ob → Type 𝓥)
                             (Id : ∀ {a} → Hom a a) (_⊙_ : ∀ {x y z} → Hom y z → Hom x y → Hom x z)
                             (lid : ∀ {x y} (p : Hom x y) → Id ⊙ p ＝ p)
                             (rid : ∀ {x y} (p : Hom x y) → p ⊙ Id ＝ p)
                             (assoc : ∀ {x y z w} (p : Hom z w) (q : Hom y z)
                                        (r : Hom x y) → p ⊙ (q ⊙ r) ＝ (p ⊙ q) ⊙ r) where


private variable
  u v w x y z : Ob
  a a' a'' b b' b'' c c' c'' d d' d'' e : Hom x y
  f g g' h h' i : Hom x y


_⟩⊙⟨_ : f ＝ h → g ＝ i → f ⊙ g ＝ h ⊙ i
_⟩⊙⟨_ = ap₂ _⊙_ 

infixr 20 _⟩⊙⟨_

module _ (a＝id : a ＝ Id) where abstract
  eliml : a ⊙ f ＝ f
  eliml {f = f} =
    a ⊙ f  ＝⟨ ap (_⊙ f) a＝id ⟩
    Id ⊙ f ＝⟨ lid f ⟩
    f      ∎

  elimr : f ⊙ a ＝ f
  elimr {f = f} =
    f ⊙ a  ＝⟨ ap (f ⊙_) a＝id ⟩
    f ⊙ Id ＝⟨ rid f ⟩
    f ∎

  elim-inner : f ⊙ (a ⊙ h) ＝ f ⊙ h
  elim-inner {f = f} = ap (f ⊙_) eliml

  introl : f ＝ a ⊙ f
  introl = sym eliml

  intror : f ＝ f ⊙ a
  intror = sym elimr

  intro-inner : f ⊙ h ＝ f ⊙ (a ⊙ h)
  intro-inner {f = f} = ap (f ⊙_) introl


module _ (ab＝c : a ⊙ b ＝ c) where abstract
  pulll : a ⊙ (b ⊙ f) ＝ c ⊙ f
  pulll {f = f} =
    a ⊙ (b ⊙ f)   ＝⟨ assoc a b f ⟩
    (a ⊙ b) ⊙ f ＝⟨ ap (_⊙ f) ab＝c ⟩
    c ⊙ f ∎

  pullr : (f ⊙ a) ⊙ b ＝ f ⊙ c
  pullr {f = f} =
    (f ⊙ a) ⊙ b ＝⟨ sym (assoc f a b) ⟩
    f ⊙ (a ⊙ b) ＝⟨ ap (f ⊙_) ab＝c ⟩
    f ⊙ c ∎

  pull-inner : (f ⊙ a) ⊙ (b ⊙ g) ＝ f ⊙ (c ⊙ g)
  pull-inner {f = f} = sym (assoc _ _ _) ∙ ap (f ⊙_) pulll

module _ (inv : h ⊙ i ＝ Id) where abstract
  cancell : h ⊙ (i ⊙ f) ＝ f
  cancell {f = f} =
    h ⊙ (i ⊙ f) ＝⟨ pulll inv ⟩
    Id ⊙ f      ＝⟨ lid f ⟩
    f           ∎

  cancelr : (f ⊙ h) ⊙ i ＝ f
  cancelr {f = f} =
    (f ⊙ h) ⊙ i ＝⟨ pullr inv ⟩
    f ⊙ Id      ＝⟨ rid f ⟩
    f           ∎

  insertl : f ＝ h ⊙ (i ⊙ f)
  insertl = sym cancell

  insertr : f ＝ (f ⊙ h) ⊙ i
  insertr = sym cancelr
