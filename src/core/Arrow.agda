module core.Arrow where

open import foundations.universe
open import foundations.Sigma
open import foundations.Functions
open import foundations.Homotopy
open import foundations.Identity
open import foundations.CoherentIsomorphism
open import foundations.QuasiIsomorphism
open import foundations.FibrePath
open import foundations.FunExt
open import ergonomics.Marker

record Arrow : Typeω where
  constructor mk-arr
  field
    {𝓤 𝓥} : Level
    {A} : Type 𝓤
    {B} : Type 𝓥
    f : A → B

module _ {𝓤 𝓥} {A : Type 𝓤} {B : Type 𝓥} (f : A → B)
         {𝓦 𝓛} {C : Type 𝓦} {D : Type 𝓛} (f' : C → D) where

  record Arrow-map : Type (𝓤 ⊔ 𝓥 ⊔ 𝓦 ⊔ 𝓛) where
    constructor mk-amap
    field
      top  : A → C
      bot  : B → D
      comm : bot ∘ f ~ f' ∘ top


  arrow-fibre :  (gs : Arrow-map) →
                 ∀ (b : B)
                 → fibre f b → fibre f' (gs .Arrow-map.bot b)
  arrow-fibre (mk-amap g g' hom) b (a , p) = (g a , sym (hom a) ∙ ap g' p)


  arrow-equiv-map : Arrow-map → Type (𝓤 ⊔ 𝓥 ⊔ 𝓦 ⊔ 𝓛)
  arrow-equiv-map a = ∀ (b : B) → is-equiv (arrow-fibre a b)
                    
module _ {𝓤 𝓥} {A : Type 𝓤} {B : Type 𝓥} {f : A → B}
         {𝓤' 𝓥'} {A' : Type 𝓤'} {B' : Type 𝓥'} {f' : A' → B'}
        {𝓤'' 𝓥''} {A'' : Type 𝓤''} {B'' : Type 𝓥''} {f'' : A'' → B''} where


  paste-squares : Arrow-map f' f'' → Arrow-map f f'
                  → Arrow-map f f''
  paste-squares (mk-amap g' h' comm') (mk-amap g h comm)
    = mk-amap (g' ∘ g) (h' ∘ h) (  h' ∘ h ∘ f        ~⟨ h' ◂ comm ⟩
                                   h' ∘ f' ∘ g       ~⟨ comm' ▸ g ⟩
                                   f'' ∘ g' ∘ g      ~∎)

  -- paste-equiv-maps : FunExtGlobal → ∀ {a : Arrow-map f' f''} {b : Arrow-map f f'}
  --                    → (ae : arrow-equiv-map _ _ a) → (be : arrow-equiv-map _ _ b)
  --                    →  arrow-equiv-map _ _ (paste-squares a b)
  -- paste-equiv-maps fe {a} {b} ae be x
  --   = tr is-equiv (WithFunExt.funext→ fe (I x))
  --      (is-equiv-∘ {f = arrow-fibre _ _ a (b .Arrow-map.bot x)} {g = arrow-fibre f f' b x}
  --        (ae (b .Arrow-map.bot x))
  --        (be x)) where
  --   module b = is-equiv (be x)
  --   module a = is-equiv (ae (b .Arrow-map.bot x))

  --   open Arrow-map

  --   II : (x : B) (fib : fibre f x) →
  --      sym (paste-squares a b .Arrow-map.comm (fib .fst)) ∙
  --        ap (paste-squares a b .Arrow-map.bot) (fib .snd)
  --       ＝
  --      (arrow-fibre f' f'' a (b .Arrow-map.bot x) ∘ arrow-fibre f f' b x)
  --        fib .snd
  --   II x (aa , p) = sym (paste-squares a b .comm aa) ∙ ap (paste-squares a b .bot) p                        ＝⟨⟩
  --              sym (ap (a .bot) (b .comm aa) ∙ ⌜ a .comm (b .top aa) ∙ refl ⌝) ∙ ap (a .bot ∘ b .bot) p     ＝⟨ {!!} ⟩
  --              ⌜ sym (ap (a .bot) (b .comm aa) ∙ a .comm (b .top aa)) ⌝ ∙ ap (a .bot ∘ b .bot) p            ＝⟨ {!!} ⟩
  --              sym (a .comm (b .top aa)) ∙ ⌜ sym (ap (a .bot) (b .comm aa)) ⌝ ∙ ap (a .bot ∘ b .bot) p      ＝⟨ {!!} ⟩
  --              sym (a .comm (b .top aa)) ∙ ap (a .bot) (sym (b .comm aa)) ∙ ⌜ ap (a .bot ∘ b .bot) p ⌝      ＝⟨ {!!} ⟩
  --              sym (a .comm (b .top aa)) ∙ ⌜ ap (a .bot) (sym (b .comm aa)) ∙ ap (a .bot) (ap (b .bot) p) ⌝ ＝⟨ {!!} ⟩ 
  --              sym (a .comm (b .top aa)) ∙ ap (a .bot) (sym (b .comm aa) ∙ ap (b .bot) p)                   ＝⟨⟩ 
  --              (arrow-fibre f' f'' a (b .bot x) ∘ arrow-fibre f f' b x) (aa , p) .snd ∎


  --   I : (x : B) →
  --     arrow-fibre _ _ a (b .Arrow-map.bot x) ∘ arrow-fibre _ _ b x
  --       ~
  --     arrow-fibre _ _ (paste-squares a b) x
  --   I x fib = fibre-path→ (refl , II x fib)

    
