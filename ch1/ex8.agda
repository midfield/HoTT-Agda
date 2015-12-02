{-# OPTIONS --without-K #-}

module ch1.ex8 where

open import HottPrelude

open import ch1.ex4 public

-- Define multiplication and exponentiation using recN . Verify that (N, +, 0,
-- ×, 1) is a semiring using only indN. You will probably also need to use
-- symmetry and transitivity of equality, Lemmas 2.1.1 and 2.1.2.

double : ℕ → ℕ
double = rec_ℕ zero (λ x y → suc (suc y))

add : ℕ → ℕ → ℕ
add = rec_ℕ (λ x → x) (λ x g m → suc (g m))

mult : ℕ → ℕ → ℕ
mult = rec_ℕ (λ x → zero) (λ x g m → add m (g m))

check_mult_a : mult 0 1 ≡ 0
check_mult_a = idp

check_mult_b : mult 100 1 ≡ 100
check_mult_b = idp

check_mult_c : mult 1 20 ≡ 20
check_mult_c = idp

check_mult_d : mult 2 4 ≡ 8
check_mult_d = idp

check_mult_e : mult 1 0 ≡ 0
check_mult_e = idp

exp : ℕ → ℕ → ℕ
exp b e = exp' e b
  where exp' = rec_ℕ (λ x → 1) (λ x g m → mult m (g m))

check_exp_a : exp 10 0 ≡ 1
check_exp_a = idp

check_exp_b : exp 0 0 ≡ 1
check_exp_b = idp

check_exp_c : exp 0 10 ≡ 0
check_exp_c = idp

check_exp_d : exp 3 3 ≡ 27
check_exp_d = idp

-- induction
ind_ℕ : ∀ {i} {C : ℕ → Type i} → C 0 → ((n : ℕ) → C n → C (suc n))
      → ((n : ℕ) → C n)
ind_ℕ c0 cs 0 = c0
ind_ℕ c0 cs (suc n) = cs n (ind_ℕ c0 cs n)

-- show ℕ is a semi-ring
-- add is associative
add_assoc : (x y z : ℕ) → add x (add y z) ≡ add (add x y) z
add_assoc = ind_ℕ add_assoc_z add_assoc_s where
  add_assoc_z : (y z : ℕ) → add 0 (add y z) ≡ add (add 0 y) z
  add_assoc_z y z = idp
  add_assoc_s : (n : ℕ)
              → ((y z : ℕ) → (add n (add y z) ≡ add (add n y) z))
              → ((y z : ℕ) → (add (suc n) (add y z) ≡ add (add (suc n) y) z))
  add_assoc_s n fi y z = ap suc (fi y z)

-- add has (left) zero
add_lzero : (x : ℕ) → add 0 x ≡ x
add_lzero x = idp

-- add has (right) zero
add_rzero : (x : ℕ) → add x 0 ≡ x
add_rzero = ind_ℕ add_rzero_z add_rzero_s where
  add_rzero_z = idp
  add_rzero_s : (n : ℕ) → add n 0 ≡ n → add (suc n) 0 ≡ suc n
  add_rzero_s n fi = ap suc fi

-- add is commutative
-- lemma first
add_suc : (x y : ℕ) → add (suc x) y ≡ add x (suc y)
add_suc = ind_ℕ add_suc_z add_suc_s where
  add_suc_z = λ y → idp
  add_suc_s : (n : ℕ)
    → ((y : ℕ) → add (suc n) y ≡ add n (suc y))
    → (y : ℕ) → add (suc (suc n)) y ≡ add (suc n) (suc y)
  add_suc_s n fi y = ap suc (fi y)

add_comm : (x y : ℕ) → add x y ≡ add y x
add_comm = ind_ℕ add_comm_z add_comm_s where
  add_comm_z : (y : ℕ) → add 0 y ≡ add y 0
  add_comm_z y = trans (add_lzero y) (sym (add_rzero y))
  add_comm_s : (n : ℕ)
    → ((y : ℕ) → add n y ≡ add y n)
    → ((y : ℕ) → add (suc n) y ≡ add y (suc n))
  add_comm_s n fi y = trans (ap suc (fi y)) (add_suc y n)

-- mult units
mult_left_z : (x : ℕ) → mult 0 x ≡ 0
mult_left_z _ = idp

mult_right_z : (x : ℕ) → mult x 0 ≡ 0
mult_right_z = ind_ℕ idp (λ n ih → ap (add 0) ih)

mult_left_u : (x : ℕ) → mult 1 x ≡ x
mult_left_u = add_rzero

mult_right_u : (x : ℕ) → mult x 1 ≡ x
mult_right_u = ind_ℕ idp (λ n ih → ap suc ih)

mult_comm0 : (x y : ℕ) → mult x (suc y) ≡ add x (mult x y)
mult_comm0 = ind_ℕ mult_comm0_z mult_comm0_s where
  mult_comm0_z = λ y → idp
  mult_comm0_s : (n : ℕ)
    → ((y : ℕ) → mult n (suc y) ≡ add n (mult n y))
    → (y : ℕ) → mult (suc n) (suc y) ≡ add (suc n) (mult (suc n) y)
  mult_comm0_s n ih y =
    mult (suc n) (suc y) =⟨ idp ⟩
    add (suc y) (mult n (suc y)) =⟨ ap (add (suc y)) (ih y) ⟩
    add (suc y) (add n (mult n y)) =⟨ add_assoc (suc y) n (mult n y) ⟩
    add (add (suc y) n) (mult n y) =⟨ ap (λ e → add (suc e) (mult n y)) (add_comm y n) ⟩
    add (add (suc n) y) (mult n y) =⟨ sym (add_assoc (suc n) y (mult n y)) ⟩
    add (suc n) (mult (suc n) y) ∎

mult_comm : (x y : ℕ) → mult x y ≡ mult y x
mult_comm = ind_ℕ mult_comm_z mult_comm_s where
  mult_comm_z = λ y → sym (mult_right_z y)
  mult_comm_s : (n : ℕ)
    → ((y : ℕ) → mult n y ≡ mult y n)
    → (y : ℕ) → mult (suc n) y ≡ mult y (suc n)
  mult_comm_s n ih y =
    mult (suc n) y =⟨ ap (add y) (ih y) ⟩
    add y (mult y n) =⟨ sym (mult_comm0 y n) ⟩
    mult y (suc n) ∎

-- the rest of this is equally painful and is much easier to do using pattern
-- matching.
