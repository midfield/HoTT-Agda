{-# OPTIONS --without-K #-}

module ch2.ex1 where

open import HottPrelude

{-

Show that the three obvious proofs of Lemma 2.1.2 are pairwise equal.

N.B. i think to show this as stated, one requires funext.  we show they are
pointwise equal.

-}

pf1 : ∀ {i} {A : Type i} {x y z : A} → x ≡ y → y ≡ z → x ≡ z
pf1 idp idp = idp

pf2 : ∀ {i} {A : Type i} {x y z : A} → x ≡ y → y ≡ z → x ≡ z
pf2 idp q = q

pf3 : ∀ {i} {A : Type i} {x y z : A} → x ≡ y → y ≡ z → x ≡ z
pf3 p idp = p

pf12 : ∀ {i} {A : Type i} {x y z : A}
     → (p : x ≡ y) → (q : y ≡ z) → pf1 p q ≡ pf2 p q
pf12 idp idp = idp

pf13 : ∀ {i} {A : Type i} {x y z : A}
     → (p : x ≡ y) → (q : y ≡ z) → pf1 p q ≡ pf3 p q
pf13 idp idp = idp

pf23 : ∀ {i} {A : Type i} {x y z : A}
     → (p : x ≡ y) → (q : y ≡ z) → pf2 p q ≡ pf3 p q
pf23 idp idp = idp

