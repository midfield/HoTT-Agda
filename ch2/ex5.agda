{-# OPTIONS --without-K #-}

module ch2.ex5 where

open import HottPrelude

{-

Prove that the functions (2.3.6) and (2.3.7) are inverse equivalences.

(2.3.6) : (f(x) = f(y)) → (p_*(f(x)) = f(y))
(2.3.7) : (p_*(f(x)) = f(y)) → (f(x) = f(y))

blee

p_*(u) := transport B p u

Given a type family (fibration) P : A → U, and x, y : A, p : x ≡ y, and

-}

transportconst : ∀ {i j} {A : Type i} {B : Type j} {x y : A}
  → (p : x ≡ y) → (f : A → B)
  → (b : B) → transport (λ _ → B) p b ≡ b
transportconst idp _ _ = idp

eq236 : ∀ {i j} {A : Type i} {B : Type j} {x y : A}
  → (p : x ≡ y) → (f : A → B)
  → f x ≡ f y → transport (λ _ → B) p (f x) ≡ f y
eq236 {i} {j} {A} {B} {x} {y} p f q = trans (transportconst p f (f x)) q


eq237 : ∀ {i j} {A : Type i} {B : Type j} {x y : A}
  → (p : x ≡ y) → (f : A → B)
  → transport (λ _ → B) p (f x) ≡ f y → f x ≡ f y
eq237 {i} {j} {A} {B} {x} {y} p f r = trans (sym (transportconst p f (f x))) r


ex5pf : ∀ {i j} {A : Type i} {B : Type j} {x y : A}
  → (p : x ≡ y) → (f : A → B) → is-equiv (eq236 p f)
ex5pf {i} {j} {A} {B} {x} {y} p f =
  record {
    g = {!!} ;
    f-g = {!!} ;
    g-f = {!!} ;
    adj = {!!}
  }
