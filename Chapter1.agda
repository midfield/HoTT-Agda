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

module ex1-5 where

  -- coproduct type in BrutalPreface is ∨

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
  indl_⊕ _ _ _ _ = refl

  indr_⊕ : ∀ {i j} {A B : Set i}
         → (C : A ⊕ B → Set j)
         → (g0 : (a : A) → C (inl_⊕ a)) → (g1 : (b : B) → C (inr_⊕ b))
         → (b : B) → ind_⊕ C g0 g1 (inr_⊕ b) ≡ g1 b
  indr_⊕ _ _ _ _ = refl
