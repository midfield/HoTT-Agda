{-# OPTIONS --without-K #-}

module ch2.ex4 where

open import HottPrelude

{-

Define, by induction on n, a general notion of n-dimensional path in a type A,
simultaneously with the type of boundaries for such paths.

-}

NPath : ∀ {i} → ℕ → Type i → Type _
NPath 0 A = A
NPath (suc n) A = Σ (NPath n A × NPath n A) λ { (x , y) → x ≡ y }
