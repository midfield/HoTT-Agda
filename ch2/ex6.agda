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

lem2 : ∀ {i} {A : Type i} {x y : A}
     → (p : x ≡ y)
     → (p ∙ ! p ≡ idp)
lem2 idp = idp

lem3 : ∀ {i} {A : Type i} {x y : A}
     → (p : x ≡ y)
     → (! p ∙ p ≡ idp)
lem3 idp = idp

ex6 : ∀ {i} {A : Type i} {x y : A}
    → (p : x ≡ y)
    → is-equiv (λ q → p ∙ q)
ex6 p = record {
  g = λ q → ! p ∙ q ;
  f-g = λ b → lem1 (p ∙ (! p)) idp idp (lem2 p) ;
  g-f = {!!} ;
  adj = {!!}
  }
