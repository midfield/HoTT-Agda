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
eq236 {i} {j} {A} {B} {x} {y} p f q = transportconst p f (f x) ∙ q

eq237 : ∀ {i j} {A : Type i} {B : Type j} {x y : A}
  → (p : x ≡ y) → (f : A → B)
  → transport (λ _ → B) p (f x) ≡ f y → f x ≡ f y
eq237 {i} {j} {A} {B} {x} {y} p f r = ! (transportconst p f (f x)) ∙ r

eqf-g : ∀ {i j} {A : Type i} {B : Type j} {x y : A}
  → (p : x ≡ y) → (f : A → B)
  → (r : transport (λ _ → B) p (f x) ≡ f y)
  → eq236 p f (eq237 p f r) ≡ r
eqf-g idp f r = idp

eqg-f : ∀ {i j} {A : Type i} {B : Type j} {x y : A}
  → (p : x ≡ y) → (f : A → B)
  → (q : f x ≡ f y)
  → eq237 p f (eq236 p f q) ≡ q
eqg-f idp f q = idp

eqadj : ∀ {i j} {A : Type i} {B : Type j} {x y : A}
  → (p : x ≡ y) → (f : A → B)
  → (q : f x ≡ f y)
  → ap (eq236 p f) (eqg-f p f q) ≡ eqf-g p f (eq236 p f q)
eqadj idp f q = idp

ex5pf : ∀ {i j} {A : Type i} {B : Type j} {x y : A}
  → (p : x ≡ y) → (f : A → B) → is-equiv (eq236 p f)
ex5pf {i} {j} {A} {B} {x} {y} p f =
  record {
    g = eq237 p f ;
    f-g = eqf-g p f ;
    g-f = eqg-f p f ;
    adj = eqadj p f
  }
