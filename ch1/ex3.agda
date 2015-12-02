{-# OPTIONS --without-K #-}

module ch1.ex3 where

open import HottPrelude

{-

Derive the induction principle for products ind_A×B, using only the
projections and the propositional uniqueness principle uppt. Verify that the
definitional equalities are valid. Generalize uppt to Σ-types, and do the same
for Σ-types. (This requires concepts from Chapter 2.)

-}

-- as remarked before, it seems like we are implicitly using the standard
-- induction principle by using pattern matching here
uppt_× : ∀ {i j} {A : Set i} {B : Set j}
       → (p : A × B) → (fst p , snd p) ≡ p
uppt_× (a , b) = idp

-- induction via projections and uppt
pind_× : ∀ {i j k} {A : Set i} {B : Set j} {C : A × B → Set k}
       → (g : (a : A) → (b : B) → C (a , b))
       → (p : A × B) → C p
-- i don't know how to implement this without giving all the implicit
-- parameters.
pind_× {i} {j} {k} {A} {B} {C} g p =
  transport C (uppt_× p) (g (fst p) (snd p))

-- once again with dependent types
uppt_Σ : ∀ {i j} {A : Set i} {B : A → Set j}
       → (p : Σ A B) → (fst p , snd p) ≡ p
uppt_Σ (a , b) = idp

pind_Σ : ∀ {i j k} {A : Set i} {B : A → Set j} {C : Σ A B → Set k}
         → (g : (a : A) → (b : B a) → C (a , b))
         → (p : Σ A B) → C p
pind_Σ {i} {j} {k} {A} {B} {C} g p =
  transport C (uppt_Σ p) (g (fst p) (snd p))

