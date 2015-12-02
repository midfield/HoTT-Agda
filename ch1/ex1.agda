{-# OPTIONS --without-K #-}

module ch1.ex1 where

open import HottPrelude

{-

Given functions f : A → B and g : B → C, define their composite
g◦f:A→C. Show that we have h◦(g◦f)≡(h◦g)◦f.

-}


∘-assoc : ∀ {i j k l} {A : Set i} {B : Set j} {C : Set k} {D : Set l}
        → (f : A → B) → (g : B → C) → (h : C → D)
        → (h ∘ (g ∘ f)) ≡ ((h ∘ g) ∘ f)
∘-assoc f g h = idp
