module ergonomics.Builtins where

open import foundations.Prelude

data ℕ : Type where
  zero : ℕ
  suc : ℕ → ℕ

{-# BUILTIN NATURAL ℕ #-}

data Bool : Type where
  true false : Bool

{-# BUILTIN BOOL Bool #-}
{-# BUILTIN TRUE true #-}
{-# BUILTIN FALSE false #-}

_<ℕ_ : ℕ → ℕ → Bool
_ <ℕ zero = false
zero <ℕ suc y = true
suc x <ℕ suc y = x <ℕ y

{-# BUILTIN NATLESS _<ℕ_ #-}

postulate
  String : Type
{-# BUILTIN STRING String #-}

postulate
  Word64 : Type

{-# BUILTIN WORD64 Word64 #-}

postulate
  Float : Type

{-# BUILTIN FLOAT Float #-}

postulate
  Char : Type

{-# BUILTIN CHAR Char #-}


infixr 5 _∷_ 

data List {𝓤} (A : Type 𝓤) : Type 𝓤 where
  [] : List A
  _∷_ : A → List A → List A

{-# BUILTIN LIST List #-}

data Maybe {𝓤} (A : Type 𝓤) : Type 𝓤 where
  nothing : Maybe A
  just : A → Maybe A

{-# BUILTIN MAYBE Maybe #-}

Maybe-map : ∀ {𝓤 𝓥} {A : Type 𝓤} {B : Type 𝓥}
            → (f : A → B)
            → Maybe A → Maybe B
Maybe-map f nothing = nothing
Maybe-map f (just x) = just (f x)

module DoMaybe where
  _>>=_ : ∀ {𝓤 𝓥} {A : Type 𝓤} {B : Type 𝓥} → Maybe A → (A → Maybe B) → Maybe B
  nothing >>= f = nothing
  just x >>= f = f x

  _>>_ : ∀ {𝓤 𝓥} {A : Type 𝓤} {B : Type 𝓥} → Maybe A → Maybe B → Maybe B
  x >> y = x >>= λ _ → y
