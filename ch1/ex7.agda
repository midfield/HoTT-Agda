{-# OPTIONS --without-K #-}

module ch1.ex7 where

open import HottPrelude

-- Give an alternative derivation of ind0=A from ind=A which avoids the use of
-- universes. (This is easiest using concepts from later chapters.)

-- path induction
pathi : ∀ {i} {j} {A : Type i}
  → (C : (a : A) (b : A) → a ≡ b → Type j)
  → ((x : A) → C x x idp)
  → ((x : A) → (y : A) → (p : x ≡ y) → C x y p)
pathi C c .x x idp = c x

bpathi : ∀ {i} {j} {A : Type i}
  → (a : A)
  → (C : (x : A) → a ≡ x → Type j)
  → C a idp
  → ((x : A) → (p : a ≡ x) → C x p)
bpathi a C c .a idp = c

-- something something J something Paulin-Mohring

-- save for later

