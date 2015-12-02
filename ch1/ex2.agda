{-# OPTIONS --without-K #-}

module ch1.ex2 where

open import HottPrelude

{-

Derive the recursion principle for products recA×B using only the projections,
and verify that the definitional equalities are valid.

-}

{-

there's something i don't understand here.  it seems impossible to define a
function in agda on products without using pattern matching.  in a sense,
pattern matching *is* the recursor for products.

e.g. the definition of the recursor uses pattern matching

rec_Σ : {A C : Set}{B : A → Set}
       → ((a : A) → B a → C) → Σ A B → C
rec_Σ g (a , b) = g a b

-}

-- recursor via projections
prec_× : ∀ {i j k} {A : Set i} {B : Set j} {C : Set k}
       → (A → B → C) → A × B → C
prec_× g p = g (fst p) (snd p)

-- recursor satisfies definition definitionally
def_prec_× : ∀ {i j k} {A : Set i} {B : Set j} {C : Set k}
           → (g : A → B → C) → (p : A × B)
           → prec_× g p ≡ g (fst p) (snd p)
def_prec_× g p = idp

{-

Do the same for Σ-types.

-}

-- recursor via projections
prec_Σ : ∀ {i j k} {A : Set i} {B : A → Set j} {C : Set k}
       → ((a : A) → B a → C) → Σ A B → C
prec_Σ g p = g (fst p) (snd p)

-- recursor satisfies definition
def_prec_Σ : ∀ {i j k} {A : Set i} {B : A → Set j} {C : Set k}
             (g : (a : A) → B a → C) (a : A)(b : B a)
           → prec_Σ g (a , b) ≡ g a b
def_prec_Σ g a b = idp
