{-# OPTIONS --without-K #-}

module HottPrelude where

-- a lot of this is stolen from HoTT-Agda

open import Agda.Primitive public using (lzero)
  renaming (Level to ULevel; lsuc to lsucc; _⊔_ to lmax)

module Universe where
  Type : (i : ULevel) → Set (lsucc i)
  Type i = Set i

  Type₀ = Type lzero
  Type0 = Type lzero

  Type₁ = Type (lsucc lzero)
  Type1 = Type (lsucc lzero)

open Universe public


module Void where
  data Empty : Type0 where

  ¬ : ∀ {i} (A : Type i) → Type i
  ¬ A = A → Empty

open Void public

record Unit : Type₀ where
  constructor unit


module Equality where
  infix 30 _≡_
  data _≡_ {i} {A : Type i} (a : A) : A → Type i where
    idp : a ≡ a -- also known as refl

  Path = _≡_

  {-# BUILTIN EQUALITY _≡_ #-}
  {-# BUILTIN REFL  idp #-}

  sym : ∀ {i} {A : Type i} {x y : A}
      → (x ≡ y) → (y ≡ x)
  sym idp = idp

  trans : ∀ {i} {A : Type i} {x y z : A}
        → (x ≡ y) → (y ≡ z) → (x ≡ z)
  trans idp idp = idp

  {- Dependent paths

  The notion of dependent path is a very important notion.
  If you have a dependent type [B] over [A], a path [p : x ≡ y] in [A] and two
  points [u : B x] and [v : B y], there is a type [u ≡ v [ B ↓ p ]] of paths from
  [u] to [v] lying over the path [p].
  By definition, if [p] is a constant path, then [u ≡ v [ B ↓ p ]] is just an
  ordinary path in the fiber.
  -}

  PathOver : ∀ {i j} {A : Type i} (B : A → Type j)
    {x y : A} (p : x ≡ y) (u : B x) (v : B y) → Type j
  PathOver B idp u v = (u ≡ v)

  infix 30 PathOver
  syntax PathOver B p u v =
    u ≡ v [ B ↓ p ]

  {- Ap, coe and transport

  Given two fibrations over a type [A], a fiberwise map between the two fibrations
  can be applied to any dependent path in the first fibration ([ap↓]).
  As a special case, when [A] is [Unit], we find the familiar [ap] ([ap] is
  defined in terms of [ap↓] because it shouldn’t change anything for the user
  and this is helpful in some rare cases)
  -}

  {- blee

  ap is cong, transport is subst.

  topologically: given two fibrations B → A, C → A, and a fibrewise map g (in
  the slash category), a path p ∈ u ≡ v in B over a path x ≡ y in A, you get a
  path [ap⇣ g p] = g u ≡ g v in C over X ≡ y in A.

  if A is a point, a path in p in B gives a path [ap g p] in C.

  for a single fibration B → A, a section f:A → B, and a path p in A, you get a
  path [apd p] in B over p.  (i don't see why this isn't a special case of [ap⇣]
  with B = A, C = B and the obvious maps.)

  how to interpret coe?  is Type i a "moduli space"?  the book says to think of
  the identity map Type i → Type i as a fibration.  from that point of view coe
  is a special case of transport, rather than transport being proved using coe,
  as it is in the library here.

  transport : ∀ {i j} {A : Type i} (B : A → Type j) {x y : A} (p : x ≡ y)
    → (B x → B y)
  transport B idp b = b

  coe : ∀ {i} {A B : Type i} (p : A ≡ B) → A → B
  coe {i} p = transport (λ x → x) p

  -}

  ap : ∀ {i j} {A : Type i} {B : Type j} (f : A → B) {x y : A}
    → (x ≡ y → f x ≡ f y)
  ap f idp = idp

  ap↓ : ∀ {i j k} {A : Type i} {B : A → Type j} {C : A → Type k}
    (g : {a : A} → B a → C a) {x y : A} {p : x ≡ y}
    {u : B x} {v : B y}
    → (u ≡ v [ B ↓ p ] → g u ≡ g v [ C ↓ p ])
  ap↓ g {p = idp} p = ap g p

  {-
  [apd↓] is defined in lib.PathOver. Unlike [ap↓] and [ap], [apd] is not
  definitionally a special case of [apd↓]
  -}

  apd : ∀ {i j} {A : Type i} {B : A → Type j} (f : (a : A) → B a) {x y : A}
    → (p : x ≡ y) → f x ≡ f y [ B ↓ p ]
  apd f idp = idp

  {-
  An equality between types gives two maps back and forth
  -}

  coe : ∀ {i} {A B : Type i} (p : A ≡ B) → A → B
  coe idp x = x

  coe! : ∀ {i} {A B : Type i} (p : A ≡ B) → B → A
  coe! idp x = x

  {-
  The operations of transport forward and backward are defined in terms of [ap]
  and [coe], because this is more convenient in practice.
  -}

  transport : ∀ {i j} {A : Type i} (B : A → Type j) {x y : A} (p : x ≡ y)
    → (B x → B y)
  transport B p = coe (ap B p)

  transport! : ∀ {i j} {A : Type i} (B : A → Type j) {x y : A} (p : x ≡ y)
    → (B y → B x)
  transport! B p = coe! (ap B p)

  {- equational reasoning -}
  infix  15 _∎
  infixr 10 _=⟨_⟩_

  _=⟨_⟩_ : ∀ {i} {A : Type i} (x : A) {y z : A} → x ≡ y → y ≡ z → x ≡ z
  _ =⟨ idp ⟩ idp = idp

  _∎ : ∀ {i} {A : Type i} (x : A) → x ≡ x
  _ ∎ = idp

  infixr 40 ap
  syntax ap f p = p |in-ctx f

open Equality public

module Function where
  -- dependent function composition
  _∘_ : ∀ {a b c}
    → {A : Type a} {B : A → Type b} {C : {x : A} → B x → Type c}
    → (f : {x : A} → (y : B x) → C y)
    → (g : (x : A) → B x)
    → ((x : A) → C (g x))
  (f ∘ g) x = f (g x)

  -- nondependent function composition
  _∘'_ : ∀ {a b c}
    → {A : Type a} {B : Type b} {C : Type c}
    → (B  → C) → (A → B) → (A → C)
  (f ∘' g) x = f (g x)

open Function public

module FunExt where
{- here is a naive definition of function extensionality

  postulate fext : ∀ {i j} {A : Type i} {B : A → Type j} {f g : (a : A) → B a}
                → ((x : A) → f x ≡ g x) → f ≡ g

  however this is not strong enough to prove useful stuff, like ex 1.6.  we need
  quasi-equivlance. -}

  -- taken from the book / HoTT-Agda

  happly : ∀ {i j} {A : Type i} {B : A → Type j} (f g : (a : A) → B a)
         → (f ≡ g) → ((x : A) → f x ≡ g x)
  happly f .f idp x = idp
--  happly f g p x = ap (λ u → u x) p

  happly2 : ∀ {i j} {A : Type i} {B : A → Type j} {f g : (a : A) → B a}
         → (f ≡ g) → ((x : A) → f x ≡ g x)
  happly2 {f} {g} idp x = idp

  record is-equiv {i j} {A : Type i} {B : Type j} (f : A → B) : Type (lmax i j)
    where
    field
      g : B → A
      f-g : (b : B) → f (g b) ≡ b
      g-f : (a : A) → g (f a) ≡ a
      adj : (a : A) → ap f (g-f a) ≡ f-g (f a)

  postulate
    funext : ∀ {i j} {A : Type i} {B : A → Type j} (f g : (a : A) → B a)
           → is-equiv (happly f g)

--  postulate
--    funext2 : ∀ {i j} {A : Type i} {B : A → Type j} (f g : (a : A) → B a)
--           → is-equiv (happly2 {f} {g})

open FunExt public

module Boolean where

  data Bool : Type₀ where
    true : Bool
    false : Bool

  if_then_else_ : ∀ {i} {A : Bool → Type i}
    (b : Bool) (t : A true) (e : A false)
    → A b
  if true then t else e = t
  if false then t else e = e

  -- fancy if-then-else
  rec_Bool : ∀ {i} {A : Set i} → A → A → Bool → A
  rec_Bool c0 c1 b = if b then c0 else c1

open Boolean public

module Product where
  -- dependent product
  infixr 60 _,_

  record Σ {i j} (A : Type i) (B : A → Type j) : Type (lmax i j) where
    constructor _,_
    field
      fst : A
      snd : B fst
  open Σ public

  _×_ : ∀ {α β} (A : Type α) (B : Type β) → Type (lmax α β)
  A × B = Σ A (λ _ → B)

open Product public

module Coproduct where

  data Coprod {i j} (A : Type i) (B : Type j) : Type (lmax i j) where
    inl : A → Coprod A B
    inr : B → Coprod A B

  _⊔_ = Coprod

  match_withl_withr_ : ∀ {i j k} {A : Type i} {B : Type j}
    {C : Coprod A B → Type k}
    (x : Coprod A B) (l : (a : A) → C (inl a)) (r : (b : B) → C (inr b)) → C x
  match (inl a) withl l withr r = l a
  match (inr b) withl l withr r = r b

open Coproduct public

module Nat where
  data ℕ : Type0 where
    zero : ℕ
    suc  : (n : ℕ) → ℕ

  {-# BUILTIN NATURAL ℕ #-}

open Nat public
