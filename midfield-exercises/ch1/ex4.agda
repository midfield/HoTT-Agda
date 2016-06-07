{-# OPTIONS --without-K #-}

module ch1.ex4 where

open import HottPrelude

{-

Assuming as given only the iterator for natural numbers

iter : Π(C:U) C → (C → C) → N → C

with the defining equations

iter(C, c0, cs, 0) := c0,
iter(C, c0, cs, succ(n)) := cs(iter(C, c0, cs, n)),

derive a function having the type of the recursor recN. Show that the defining
equations of the recursor hold propositionally for this function, using the
induction principle for N.

-}

-- recursor
rec_ℕ : ∀ {i} {C : Set i} → C → (ℕ → C → C) → ℕ → C
rec_ℕ c0 cs 0 = c0
rec_ℕ c0 cs (suc n) = cs n (rec_ℕ c0 cs n)

-- iterator
iter : ∀ {i} {C : Set i} → C → (C → C) → ℕ → C
iter c0 cs 0 = c0
iter c0 cs (suc n) = cs (iter c0 cs n)

irec_help : ∀ {i} {C : Set i} → (ℕ → C → C) → (ℕ × C → ℕ × C)
irec_help {i} {C} cs (n , x) = (suc n , cs n x)

-- recursor from iterator
irec_ℕ : ∀ {i} {C : Set i} → C → (ℕ → C → C) → ℕ → C
irec_ℕ {i} {C} c0 cs n = snd (iter {i} {ℕ × C} (0 , c0) (irec_help cs) n)

{-

equivalence of recursor definitions

iter(C',c0',cs',0) === (0,c0) === (0,rec(C,c0,cs,0))
iter(C',c0',cs',succ(n)) === cs'(iter(C',c0',cs',n))
=== cs'(n, rec(C,c0,cs,n)) === (succ(n), cs(n)(rec(C,c0,cs,n)))
=== (succ(n),rec(C,c0,cs,succ(n)))

so rec(C,c0,cs,n) === snd(iter(C',c0',cs',n)).

-}

irec_lemma : ∀ {i} {C : Set i} → (c0 : C) → (cs : ℕ → C → C) → (n : ℕ)
           → iter (0 , c0) (irec_help cs) n ≡ (n , rec_ℕ c0 cs n)
irec_lemma c0 cs 0 = idp
irec_lemma c0 cs (suc n) = ap (irec_help cs) (irec_lemma c0 cs n)

eq_rec_ℕ : ∀ {i} {C : Set i} → (c0 : C) → (cs : ℕ → C → C) → (n : ℕ)
         → irec_ℕ c0 cs n ≡ rec_ℕ c0 cs n
eq_rec_ℕ c0 cs n = ap snd (irec_lemma c0 cs n)
