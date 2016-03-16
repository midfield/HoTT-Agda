{-# OPTIONS --without-K #-}

open import HottPrelude

module ch2.ex7 where

{-

State and prove a generalization of Theorem 2.6.5 from cartesian products to
Σ-types.

-}

-- note that pair= in the book is different from pair= in HoTT-Agda

-- nondependent version
pair-ap' : ∀ {i} {A B A' B' : Type i} (g : A → A') (h : B → B')
  → A × B → A' × B'
pair-ap' g h x = (g (fst x) , h (snd x))

pair=' : ∀ {i} {A B : Type i} {x y : A × B}
  → (fst x ≡ fst y) × (snd x ≡ snd y) → x ≡ y
pair=' (idp , idp) = idp

theorem-265' : ∀ {i} {A B A' B' : Type i} (g : A → A') (h : B → B')
  → (x y : A × B) → (p : fst x ≡ fst y) → (q : snd x ≡ snd y)
  → ap (pair-ap' g h) (pair=' (p , q)) ≡ pair=' (ap g p , ap h q)
theorem-265' = {!!}

-- dependent version
pair-ap : ∀ {i j} {A A' : Type i} {B : A → Type j} {B' : A' → Type j}
  → (g : A → A') → (h : (a : A) → B a → B' (g a))
  → Σ A B → Σ A' B'
pair-ap g h x = (g (fst x), h (fst x) (snd x))

pair= : ∀ {i j} {A : Type i} {B : A → Type j} {x y : Σ A B}
  → Σ (fst x ≡ fst y) (λ p → transport B p (snd x) ≡ snd y)
  → x ≡ y
pair= = {!!} --(idp , idp) = idp

theorem-265 : ∀ {i j} {A A' : Type i} {B : A → Type j} {B' : A' → Type j}
  → (g : A → A') → (h : (a : A) → B a → B' (g a))
  → (x y : Σ A B) → (p : fst x ≡ fst y) → (q : transport B p (snd x) ≡ snd y)
  → ap (pair-ap g h) (pair= (p , q)) ≡ pair= (ap g p , ap h q)
-- → ?
theorem-265 = {!!}
