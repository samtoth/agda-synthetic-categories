module ufAxioms where

open import foundations.Prelude

open import axioms.FunExt public



open import foundations.Univalence

postulate
  UA : Univalence


open WithGlobalUnivalence UA public

-- {-# REWRITE ua-linv #-}

open import axioms.Interval public

open import axioms.Pushout public

