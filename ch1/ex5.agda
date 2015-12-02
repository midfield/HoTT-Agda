{-# OPTIONS --without-K #-}

module ch1.ex5 where

open import HottPrelude

{-

Show that if we define A + B := Σ(x:2) rec2(U, A, B, x), then we can give a
definition of indA+B for which the definitional equalities stated in §1.7 hold.

-}

-- coproduct via dependent pairs.  i think there's no reason to have A and B
-- in different universes, we can always change universes
_⊕_ : ∀ {i} (A B : Set i) → Set i
A ⊕ B = Σ Bool (rec_Bool A B)

-- "constructors"
inl_⊕ : ∀ {i} {A B : Set i} (a : A) → A ⊕ B
inl_⊕ a = true , a

inr_⊕ : ∀ {i} {A B : Set i} (b : B) → A ⊕ B
inr_⊕ b = false , b

-- induction
ind_⊕ : ∀ {i j} {A B : Set i}
      → (C : A ⊕ B → Set j)
      → (g0 : (a : A) → C (inl_⊕ a)) → (g1 : (b : B) → C (inr_⊕ b))
      → (s : (A ⊕ B)) → C s
ind_⊕ _ g0 _ (true , a) = g0 a
ind_⊕ _ _ g1 (false , b) = g1 b

-- proofs
indl_⊕ : ∀ {i j} {A B : Set i}
       → (C : A ⊕ B → Set j)
       → (g0 : (a : A) → C (inl_⊕ a)) → (g1 : (b : B) → C (inr_⊕ b))
       → (a : A) → ind_⊕ C g0 g1 (inl_⊕ a) ≡ g0 a
indl_⊕ _ _ _ _ = idp

indr_⊕ : ∀ {i j} {A B : Set i}
       → (C : A ⊕ B → Set j)
       → (g0 : (a : A) → C (inl_⊕ a)) → (g1 : (b : B) → C (inr_⊕ b))
       → (b : B) → ind_⊕ C g0 g1 (inr_⊕ b) ≡ g1 b
indr_⊕ _ _ _ _ = idp

