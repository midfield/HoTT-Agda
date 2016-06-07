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
  → {x y : A × B} → (p : fst x ≡ fst y) → (q : snd x ≡ snd y)
  → ap (pair-ap' g h) (pair=' (p , q)) ≡ pair=' (ap g p , ap h q)
theorem-265' _ _ idp idp = idp

-- dependent version
pair-ap : ∀ {i j} {A A' : Type i} {B : A → Type j} {B' : A' → Type j}
  → (g : A → A') → (h : (a : A) → B a → B' (g a))
  → Σ A B → Σ A' B'
pair-ap g h x = (g (fst x), h (fst x) (snd x))

pair= : ∀ {i j} {A : Type i} {B : A → Type j} {x y : Σ A B}
  → Σ (fst x ≡ fst y) (λ p → transport B p (snd x) ≡ snd y)
  → x ≡ y
pair= (idp , idp) = idp

theorem-265 : ∀ {i j} {A A' : Type i} {B : A → Type j} {B' : A' → Type j}
  → (g : A → A') → (h : (a : A) → B a → B' (g a))
  → {x y : Σ A B} → (p : fst x ≡ fst y) → (q : transport B p (snd x) ≡ snd y)
  → {!!}
--  → pair-ap g h (fst x , snd x) ≡ pair-ap g h (fst y , snd y)
--  → (g (fst x) , h (fst x) (snd x)) ≡ (g (fst y) , h (fst y) (snd y))
--  → ap (pair-ap g h) (pair= (p , q)) ≡ pair= (ap g p , ap (h (fst y)) q)
theorem-265 g h {x} {y} p q = ap (pair-ap g h) (pair= (p , q))

-- → ap (pair-ap g h) (pair= (p , q)) ≡ pair= (ap g p , ap (h (fst y)) q)
--  → ap (pair-ap g h) -- Σ A B → Σ A' B'
--    (pair= (p , q)) -- x ≡ y
--    ≡
--    pair= (ap g p , -- g (fst x) ≡ g (fst y)
--           λ r → transport B' r (h (fst x) (snd x)) ≡ 
--           ap (h (fst y)) q) -- h (fst x) (transport B p (snd x)) ≡ h (fst x) (snd y)
--theorem-265 = {!!}

