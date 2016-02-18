{-# OPTIONS --without-K #-}

module ch2.ex3 where

open import HottPrelude
open import ch2.ex1

{-

Give a fourth, different, proof of Lemma 2.1.2, and prove that it is equal to the others.

-}

-- extra credit
pf4 : ∀ {i} {A : Type i} {x y z : A} → x ≡ y → y ≡ z → x ≡ z
pf4 {_} {_} {x} {_} {_} p q = transport (λ yp → x ≡ yp) q p

pf14 : ∀ {i} {A : Type i} {x y z : A}
     → (p : x ≡ y) → (q : y ≡ z) → pf1 p q ≡ pf4 p q
pf14 idp idp = idp



