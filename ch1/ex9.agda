{-# OPTIONS --without-K #-}

module ch1.ex9 where

open import HottPrelude

-- Define the type family Fin : N → U mentioned at the end of §1.3, and the
-- dependent function fmax : Σ(n:N) Fin(n + 1) mentioned in §1.4.

Fin : ℕ → Type0
Fin zero = Empty
Fin (suc n) = Unit ⊔ Fin n

fmax : (n : ℕ) → Fin (suc n)
fmax _ = inl unit
