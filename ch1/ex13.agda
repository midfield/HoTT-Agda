{-# OPTIONS --without-K #-}

module ch1.ex13 where

open import HottPrelude

-- Using propositions-as-types, derive the double negation of the principle of
-- excluded middle, i.e. prove not (not (P or not P)).

lemma1 : ∀ {i j k} {A : Type i} {B : Type j} {C : Type k}
       → (A ⊔ B → C) → (A → C)
lemma1 f = f ∘ inl

lemma2 : ∀ {i j k} {A : Type i} {B : Type j} {C : Type k}
       → (A ⊔ B → C) → (B → C)
lemma2 f = f ∘ inr

--not-middle : ∀ {i} {A : Type i} → ¬(¬(A ⊔ ¬ A))
not-middle : ∀ {i} {A : Type i} → ((A ⊔ (A → Empty)) → Empty) → Empty
not-middle f = (lemma2 f) (lemma1 f)


