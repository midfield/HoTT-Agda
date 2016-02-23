{-# OPTIONS --without-K #-}

module ch2.ex6 where

open import HottPrelude

{-

Prove that if p : x ≡ y, then the function (p ∙ _) : (y ≡ z) → (x ≡ z) is an
equivalence.

-}

lem1 : ∀ {i} {A : Type i} {x y z : A}
     → (p r : x ≡ y) → (q : y ≡ z) → p ≡ r
     → p ∙ q ≡ r ∙ q
lem1 p r q s = ap (λ t → t ∙ q) s

ex6 : ∀ {i} {A : Type i} {x y : A}
    → (p : x ≡ y)
    → is-equiv (λ q → p ∙ q)
ex6 p = record {
  g = λ q → ! p ∙ q ;
  f-g = λ q → ! (∙-assoc p (! p) q) ∙ lem1 (p ∙ (! p)) idp q (!-inv-r p) ;
  g-f = {!!} ;
  adj = {!!}
  }
