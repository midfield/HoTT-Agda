{-# OPTIONS --without-K #-}

module ch1.ex12 where

open import HottPrelude

{-

Using the propositions as types interpretation, derive the following
tautologies.

(i) If A, then (if B then A).
(ii) If A, then not (not A).
(iii) If (not A or not B), then not (A and B).

-}

part1 : ∀ {i} {A B : Type i} → A → (B → A)
part1 a _ = a

part2 : ∀ {i} {A : Type i} → A → ¬ (¬ A)
part2 a f = f a

part3 : ∀ {i} {A B : Type i} → (¬ A ⊔ ¬ B) → ¬ (A × B)
part3 (inl na) (a , b) = na a
part3 (inr nb) (a , b) = nb b
