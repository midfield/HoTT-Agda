{-# OPTIONS --without-K #-}

module ch1.ex6 where

open import HottPrelude

{-

Show that if we define A × B := Σ(x:2) rec2(U, A, B, x), then we can give a
definition of indA×B for which the definitional equalities stated in §1.5 hold
propositionally (i.e. using equality types). (This requires the function
extensionality axiom, which is introduced in §2.9.)

-}

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
