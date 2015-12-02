{-# OPTIONS --without-K #-}

module Chapter1x where

open import HottPrelude
open import Chapter1

module ex1-9 where

  Fin : ℕ → Type0
  Fin zero = Empty
  Fin (suc n) = Unit ⊔ Fin n

  fmax : (n : ℕ) → Fin (suc n)
  fmax _ = inl unit

module ex1-10 where

  open ex1-4 public


  -- ack 0 n = suc n
  -- ack (suc m) 0 = ack m 1
  -- ack (suc m) (suc n) = ack m (ack (suc m) n)
  ack : ℕ → ℕ → ℕ
  ack = rec_ℕ c0 cs where
    -- induction on m, then induction on n
    -- c0 n = ack 0 n
    c0 : ℕ → ℕ
    c0 n = suc n
    cs : ℕ → (ℕ → ℕ) → (ℕ → ℕ)
    -- ackm n = ack m n
    cs m ackm = rec_ℕ c0' cs' where
      -- induction on n
      c0' = ackm 1
      cs' : ℕ → ℕ → ℕ
      -- acksmn = ack (suc m) n
      cs' n acksmn = ackm acksmn

  ack2 : ℕ → ℕ → ℕ
  ack2 = rec_ℕ suc (λ _ f → rec_ℕ (f 1) (λ _ → f))

  ack3 : ℕ → ℕ → ℕ
  ack3 0 n = suc n
  ack3 (suc m) 0 = ack m 1
  ack3 (suc m) (suc n) = ack m (ack (suc m) n)

module ex1-11 where

  lemma : ∀ {i} {A : Type i} → A → ¬(¬ A)
  -- a : A
  -- f : (A → Empty) → Empty
  lemma a f = f a

  prop : ∀ {i} {A : Type i} → ¬(¬(¬ A)) → ¬ A
  -- f : ((A → Empty) → Empty) → Empty
  prop f a = f (lemma a)

module ex1-12 where

  part1 : ∀ {i} {A B : Type i} → A → (B → A)
  part1 a _ = a

  part2 : ∀ {i} {A : Type i} → A → ¬ (¬ A)
  part2 a f = f a

  part3 : ∀ {i} {A B : Type i} → (¬ A ⊔ ¬ B) → ¬ (A × B)
  part3 (inl na) (a , b) = na a
  part3 (inr nb) (a , b) = nb b

