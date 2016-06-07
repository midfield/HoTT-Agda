{-# OPTIONS --without-K #-}

module ch1.ex15 where

open import HottPrelude
open import ch1.ex7 -- for path induction

{-

Show that indiscernability of identicals follows from path induction.

Indiscernability of identicals: For every family C : A → U there is a function

f : ∏_{x, y : A} ∏_{p : x ≡ y} C(x) → C(y)

such that

f(x, x, idp) = id_{C(x)}.


(note this is just "transport" or "subst".)

-}

indiscernability : ∀ {i j} {A : Type i} {C : A → Type j} →
                 (x : A) → (y : A) → (p : x ≡ y) → (C(x) → C(y))
indiscernability {i} {j} {A} {C} x .x idp =
  -- coe (ap C p)
  λ x → x

-- can this be done without pattern-matching?  take 2:
{-

indis2 : ∀ {i j} {A : Type i} (C : A → Type j) →
       (x : A) → (y : A) → (p : x ≡ y) → (C(x) → C(y))
indis2 C =

-}
