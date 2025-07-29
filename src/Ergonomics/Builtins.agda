module Ergonomics.Builtins where

open import Foundations.Prelude

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

List-map :  ∀ {𝓤 𝓥} {A : Type 𝓤} {B : Type 𝓥}
            → (f : A → B)
            → List A → List B
List-map f [] = []
List-map f (x ∷ xs) = f x ∷ List-map f xs

map-up : ∀ {𝓤 𝓥} {A : Type 𝓤} {B : Type 𝓥}
         → (ℕ → A → B) → ℕ → List A → List B
map-up f _ []       = []
map-up f n (x ∷ xs) = f n x ∷ map-up f (suc n) xs

rev-ap : ∀ {𝓤} {A : Type 𝓤}
         → List A
         → (List A → List A)
rev-ap [] ys = ys
rev-ap (x ∷ xs) ys = rev-ap xs (x ∷ ys)

reverse : ∀ {𝓤} {A : Type 𝓤}
          → List A → List A
reverse xs = rev-ap xs []

foldr : ∀ {𝓤 𝓥} {A : Type 𝓤} {B : Type 𝓥}
        → (A → B → B) → B → List A → B
foldr f b [] = b
foldr f b (x ∷ l) = f x (foldr f b l)

_++_ : ∀ {𝓤} {A : Type 𝓤} → List A → List A → List A
[] ++ ys = ys
(x ∷ xs) ++ ys = x ∷ (xs ++ ys)


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
