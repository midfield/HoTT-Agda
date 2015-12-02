{-# OPTIONS --without-K #-}

module ch1.ex10 where

open import HottPrelude

open import ch1.ex4 public

{-

Show that the Ackermann function ack : N → N → N is definable using only recN
satisfying the following equations:

ack(0, n) = succ(n),
ack(succ(m), 0) = ack(m, 1),
ack(succ(m), succ(n)) = ack(m, ack(succ(m), n)).

-}

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
