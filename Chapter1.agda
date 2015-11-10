{-# OPTIONS --without-K #-}

module Chapter1 where

open import HottPrelude

module ex1-1 where

  {-

  Given functions f : A → B and g : B → C, define their composite
  g◦f:A→C. Show that we have h◦(g◦f)≡(h◦g)◦f.

  -}


  ∘-assoc : ∀ {i j k l} {A : Set i} {B : Set j} {C : Set k} {D : Set l}
          → (f : A → B) → (g : B → C) → (h : C → D)
          → (h ∘ (g ∘ f)) ≡ ((h ∘ g) ∘ f)
  ∘-assoc f g h = idp

module ex1-2-1 where

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

module ex1-2-2 where

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

module ex1-3-1 where

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

module ex1-3-2 where

  -- once again with dependent types
  uppt_Σ : ∀ {i j} {A : Set i} {B : A → Set j}
         → (p : Σ A B) → (fst p , snd p) ≡ p
  uppt_Σ (a , b) = idp

  pind_Σ : ∀ {i j k} {A : Set i} {B : A → Set j} {C : Σ A B → Set k}
           → (g : (a : A) → (b : B a) → C (a , b))
           → (p : Σ A B) → C p
  pind_Σ {i} {j} {k} {A} {B} {C} g p =
    transport C (uppt_Σ p) (g (fst p) (snd p))

module ex1-4 where

  -- recursor
  rec_ℕ : ∀ {i} {C : Set i} → C → (ℕ → C → C) → ℕ → C
  rec_ℕ c0 cs 0 = c0
  rec_ℕ c0 cs (suc n) = cs n (rec_ℕ c0 cs n)

  -- iterator
  iter : ∀ {i} {C : Set i} → C → (C → C) → ℕ → C
  iter c0 cs 0 = c0
  iter c0 cs (suc n) = cs (iter c0 cs n)

  irec_help : ∀ {i} {C : Set i} → (ℕ → C → C) → (ℕ × C → ℕ × C)
  irec_help {i} {C} cs (n , x) = (suc n , cs n x)

  -- recursor from iterator
  irec_ℕ : ∀ {i} {C : Set i} → C → (ℕ → C → C) → ℕ → C
  irec_ℕ {i} {C} c0 cs n = snd (iter {i} {ℕ × C} (0 , c0) (irec_help cs) n)

  {-

  equivalence of recursor definitions

  iter(C',c0',cs',0) === (0,c0) === (0,rec(C,c0,cs,0))
  iter(C',c0',cs',succ(n)) === cs'(iter(C',c0',cs',n))
  === cs'(n, rec(C,c0,cs,n)) === (succ(n), cs(n)(rec(C,c0,cs,n)))
  === (succ(n),rec(C,c0,cs,succ(n)))

  so rec(C,c0,cs,n) === snd(iter(C',c0',cs',n)).

  -}

  irec_lemma : ∀ {i} {C : Set i} → (c0 : C) → (cs : ℕ → C → C) → (n : ℕ)
             → iter (0 , c0) (irec_help cs) n ≡ (n , rec_ℕ c0 cs n)
  irec_lemma c0 cs 0 = idp
  irec_lemma c0 cs (suc n) = ap (irec_help cs) (irec_lemma c0 cs n)

  eq_rec_ℕ : ∀ {i} {C : Set i} → (c0 : C) → (cs : ℕ → C → C) → (n : ℕ)
           → irec_ℕ c0 cs n ≡ rec_ℕ c0 cs n
  eq_rec_ℕ c0 cs n = ap snd (irec_lemma c0 cs n)


module RecBool where

  -- fancy if-then-else
  rec_Bool : ∀ {i} {A : Set i} → A → A → Bool → A
  rec_Bool c0 c1 b = if b then c0 else c1

open RecBool public

module ex1-5 where

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

module ex1-6 where

  -- product via dependent functions
  _⊗_ : ∀ {i} (A B : Set i) → Set i
  A ⊗ B = (t : Bool) → rec_Bool A B t

  -- "constructors"
  _,'_ : ∀ {i} {A B : Set i}
       → A → B → A ⊗ B
  _,'_ a b true = a
  _,'_ a b false = b

  -- projections
  p₁ : ∀ {i} {A B : Set i} → A ⊗ B → A
  p₁ f = f true

  p₂ : ∀ {i} {A B : Set i} → A ⊗ B → B
  p₂ f = f false

  ptwise : ∀ {i} {A B : Set i}
         → {p : A ⊗ B} → (x : Bool) → (p₁ p ,' p₂ p) x ≡ p x
  ptwise true = idp
  ptwise false = idp


  -- propositional uniqueness
  -- function extensionality is needed for propositional uniqueness
  uppt_⊗ : ∀ {i} {A B : Set i}
         → (p : A ⊗ B) → (p₁ p ,' p₂ p) ≡ p
  uppt_⊗ p = is-equiv.g (funext (p₁ p ,' p₂ p) p) ptwise

  -- induction
  ind_⊗ : ∀ {i j} {A B : Set i}
        → (C : A ⊗ B → Set j)
        → (g : (a : A) → (b : B) → C (a ,' b))
        → (p : A ⊗ B) → C p
  ind_⊗ C g p = transport C (uppt_⊗ p) (g (p₁ p) (p₂ p))

{-

taking apart how this works:

for x ∈ A ⊗ B, f = (p1 x, p2 x) and g = x are both functions (domain Bool).

H = happly takes equality of functions and gives pointwise equality.

funext postulates that happly is a quasi-isomorphism, with quasi-inverse
G = is-equiv.g funext ...

ptwise is a function which gives pointwise equivalence between equivalent
functions.

uppt = G ptwise is the quasi-inverse, e.g. gives equality between
f and g as functions.

now in the special case when x = (a , b), then in fact f and g are
definitionally equal (idp ∈ f ≡ g).  we want to show ind_⊗ C g (a , b) ≡ g a b.
it is enough to show that uppt (a , b) = G ptwise ≡ idp, since transport C idp z
= z.  (is it necessary?  if E in (transport C path z ≡ z)), can we use E to show
path ≡ idp?)

since G and H are quasi-inverses,

G (H idp) ≡ idp

this is close but not quite what we want.  (H idp) gives a pointwise equality,
but we need to show (H idp) ≡ ptwise.  this appears to require another use of
funext.

it is unfortunate that we need to use funext TWICE.  note that it appears to be
necessary: if G (ptwise) ≡ idp ≡ G (H idp), then by quasi-equivalence

H (G ptwise) ≡ ptwise ≡ H (G (H idp) ≡ H idp.

however paolo cappriotti's solution doesn't appear to use funext twice
explicitly.  maybe something to ask him.

-}

  lemma1 : ∀ {i} {A B : Set i}
         → (a : A) → (b : B)
         → happly (p₁ (a ,' b) ,' p₂ (a ,' b)) (a ,' b) idp
         ≡ ptwise {i} {A} {B} {(a ,' b)}
  lemma1 {i} {A} {B} a b = is-equiv.g (funext (λ x → idp) (ptwise {i} {A} {B} { (a ,' b) } ) )
         (λ { true → idp; false → idp })

  lemma2 : ∀ {i} {A B : Set i}
         → (a : A) → (b : B)
         →  is-equiv.g (funext (p₁ (a ,' b) ,' p₂ (a ,' b)) (a ,' b)) (happly (p₁ (a ,' b) ,' p₂ (a ,' b)) (a ,' b) idp)
         ≡ uppt_⊗ (a ,' b)
  lemma2 {i} {A} {B} a b = ap feg (lemma1 {i} {A} {B} a b)
    where
      p : A ⊗ B
      p = (a ,' b)
      feg : ((b : Bool) → (p₁ p ,' p₂ p) b ≡ p b) → ((p₁ p ,' p₂ p) ≡ p)
      feg = is-equiv.g (funext (p₁ p ,' p₂ p) p)

  lemma3 : ∀ {i} {A B : Set i}
         → (a : A) → (b : B)
         →  is-equiv.g  (funext (p₁ (a ,' b) ,' p₂ (a ,' b)) (a ,' b)) (happly (p₁ (a ,' b) ,' p₂ (a ,' b)) (a ,' b) idp) ≡ idp
  lemma3 {i} {A} {B} a b = is-equiv.g-f  (funext (p₁ (a ,' b) ,' p₂ (a ,' b)) (a ,' b)) idp

  lemma4 : ∀ {i} {A B : Set i}
         → (a : A) → (b : B)
         → uppt_⊗ (a ,' b) ≡ idp
  lemma4 {i} {A} {B} a b = trans (sym (lemma2 a b)) (lemma3 a b)

  indd_⊗ : ∀ {i j} {A B : Set i}
         → (C : A ⊗ B → Set j)
         → (g : (a : A) → (b : B) → C (a ,' b))
         → (a : A) → (b : B)
         → ind_⊗ C g (a ,' b) ≡ g a b
  indd_⊗ {i} {j} {A} {B} C g a b = ap tp (lemma4 a b)
    where
      p : A ⊗ B
      p = (a ,' b)
      tp : (p₁ p ,' p₂ p) ≡ p → C p
      tp x = transport C x (g a b)


  ind2_⊗ : ∀ {i j} {A B : Set i}
         → (C : A ⊗ B → Set j)
         → (g : (a : A) → (b : B) → C (a ,' b))
         → (a : A) → (b : B)
         → ind_⊗ C g (a ,' b) ≡ g a b
  ind2_⊗ C g a b =
    ind_⊗ C g (a ,' b) =⟨ lemma4 a b |in-ctx (λ x → transport C x (g a b)) ⟩
    g a b ∎

module ex1-7 where
  -- path induction
  pathi : ∀ {i} {j} {A : Type i}
    → (C : (a : A) (b : A) → a ≡ b → Type j)
    → ((x : A) → C x x idp)
    → ((x : A) → (y : A) → (p : x ≡ y) → C x y p)
  pathi C c .x x idp = c x

  bpathi : ∀ {i} {j} {A : Type i}
    → (a : A)
    → (C : (x : A) → a ≡ x → Type j)
    → C a idp
    → ((x : A) → (p : a ≡ x) → C x p)
  bpathi a C c .a idp = c

  -- something something J something Paulin-Mohring

  -- save for later

module ex1-8 where
  -- define multiplication and exponentiation using rec_ℕ
  open ex1-4 public

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
  add_assoc = ind_ℕ

-- add is commutative
  add_comm : {x y : ℕ} → add x y ≡ add y x
  add_comm = {!!}
