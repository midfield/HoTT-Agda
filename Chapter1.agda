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
  projl_⊗ : ∀ {i} {A B : Set i} → A ⊗ B → A
  projl_⊗ f = f true

  projr_⊗ : ∀ {i} {A B : Set i} → A ⊗ B → B
  projr_⊗ f = f false

  ptwise : ∀ {i} {A B : Set i}
         → {p : A ⊗ B} → (x : Bool) → (projl_⊗ p ,' projr_⊗ p) x ≡ p x
  ptwise true = idp
  ptwise false = idp


  -- propositional uniqueness
  -- function extensionality is needed for propositional uniqueness
  uppt_⊗ : ∀ {i} {A B : Set i}
         → (p : A ⊗ B) → (projl_⊗ p ,' projr_⊗ p) ≡ p
  uppt_⊗ p = is-equiv.g (funext (projl_⊗ p ,' projr_⊗ p) p) ptwise

{-

taking apart how this works:

for x ∈ A ⊗ B, f = (p1 x, p2 x) and g = x are both functions (domain Bool)

happly says that equality on functions gives pointwise equality

funext postulates that happly is a quasi-isomorphism, with quasi-inverse
is-equiv.g

ptwise is a function which gives pointwise equality between f and g

uppt = is-equiv.g funext ptwise is the quasi-inverse, e.g. gives equality between
f and g as functions.

now in the special case when x = (a , b), then in fact f and g are
definitionally equal (idp ∈ f ≡ g).  what is uppt_⊗ x in this case?  it would be
nice if it is equivalent to idp.

let H = happly be the forward equivalence, and G be the quasi inverse.  then
is-equiv says (if idp is equivalence of functions)

G (H idp) ≡ idp

this is close but not quite what we want.  (H idp) gives a pointwise equality,
but we need to show it is the same as λ {...}.  this appears to require another
use of funext.

-}

  -- induction
  ind_⊗ : ∀ {i j} {A B : Set i}
        → (C : A ⊗ B → Set j)
        → (g : (a : A) → (b : B) → C (a ,' b))
        → (p : A ⊗ B) → C p
  ind_⊗ C g p = transport C (uppt_⊗ p) (g (projl_⊗ p) (projr_⊗ p))


  lemma1 : ∀ {i} {A B : Set i}
         → (a : A) → (b : B)
         → happly (projl_⊗ (a ,' b) ,' projr_⊗ (a ,' b)) (a ,' b) idp
         ≡ ptwise {i} {A} {B} {(a ,' b)}
  lemma1 {i} {A} {B} a b = is-equiv.g (funext (λ x → idp) (ptwise {i} {A} {B} { (a ,' b) } ) )
         (λ { true → idp; false → idp })


  lemma2 : ∀ {i} {A B : Set i}
         → (a : A) → (b : B)
         →  is-equiv.g (funext (projl_⊗ (a ,' b) ,' projr_⊗ (a ,' b)) (a ,' b)) (happly (projl_⊗ (a ,' b) ,' projr_⊗ (a ,' b)) (a ,' b) idp)
         ≡ uppt_⊗ (a ,' b)
  lemma2 {i} {A} {B} a b = ap feg (lemma1 {i} {A} {B} a b)
    where
      p : A ⊗ B
      p = (a ,' b)
      feg : ((b : Bool) → (projl_⊗ p ,' projr_⊗ p) b ≡ p b) → ((projl_⊗ p ,' projr_⊗ p) ≡ p)
      feg = is-equiv.g (funext (projl_⊗ p ,' projr_⊗ p) p)

  lemma3 : ∀ {i} {A B : Set i}
         → (a : A) → (b : B)
         →  is-equiv.g  (funext (projl_⊗ (a ,' b) ,' projr_⊗ (a ,' b)) (a ,' b)) (happly (projl_⊗ (a ,' b) ,' projr_⊗ (a ,' b)) (a ,' b) idp) ≡ idp
  lemma3 {i} {A} {B} a b = is-equiv.g-f  (funext (projl_⊗ (a ,' b) ,' projr_⊗ (a ,' b)) (a ,' b)) idp

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
      tp : (projl_⊗ p ,' projr_⊗ p) ≡ p → C p
      tp x = transport C x (g a b)


  ind2_⊗ : ∀ {i j} {A B : Set i}
         → (C : A ⊗ B → Set j)
         → (g : (a : A) → (b : B) → C (a ,' b))
         → (a : A) → (b : B)
         → ind_⊗ C g (a ,' b) ≡ g a b
  ind2_⊗ {i} {j} {A} {B} C g a b =
    ind_⊗ C g (a ,' b) =⟨ idp ⟩
    transport C (uppt_⊗ (a ,' b)) (g (projl_⊗ (a ,' b)) (projr_⊗ (a ,' b))) =⟨ {!!} ⟩
    g a b ∎
