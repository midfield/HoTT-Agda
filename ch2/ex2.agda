{-# OPTIONS --without-K #-}

module ch2.ex2 where

open import HottPrelude
open import ch2.ex1

{-

Show that the three equalities of proofs constructed in the previous exercise
form a commutative triangle. In other words, if the three definitions of
concatenation are denoted by (p ∘1 q), (p ∘2 q), and (p ∘3 q), then the
concatenated equality

(p ∘1 q) = (p ∘2 q) = (p ∘3 q)

is equal to the equality (p ∘1 q) = (p ∘3 q).

-}

triangle : ∀ {i} {A : Type i} {x y z : A}
  → (p : x ≡ y) (q : y ≡ z)
  → (pf12 p q ∙ pf23 p q) ≡ (pf13 p q)
triangle idp idp = idp
