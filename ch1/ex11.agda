{-# OPTIONS --without-K #-}

module ch1.ex11 where

open import HottPrelude

-- Show that for any type A, we have ¬¬¬A → ¬A.

double-neg : ∀ {i} {A : Type i} → A → ¬(¬ A)
-- a : A
-- f : (A → Empty) → Empty
double-neg a f = f a

triple-neg-elim : ∀ {i} {A : Type i} → ¬(¬(¬ A)) → ¬ A
-- f : ((A → Empty) → Empty) → Empty
triple-neg-elim f a = f (double-neg a)
