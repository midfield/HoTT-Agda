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

module Equality where
  infix 30 _≡_
  data _≡_ {i} {A : Type i} (a : A) : A → Type i where
    idp : a ≡ a -- also known as refl

  Path = _≡_

  {-# BUILTIN EQUALITY _≡_ #-}
  {-# BUILTIN REFL  idp #-}

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


  {- ap is cong, transport is subst -}

open Equality public

module Function where
  -- dependent function composition
  _∘_ : ∀ {a b c}
    → {A : Set a} {B : A → Set b} {C : {x : A} → B x → Set c}
    → (f : {x : A} → (y : B x) → C y)
    → (g : (x : A) → B x)
    → ((x : A) → C (g x))
  (f ∘ g) x = f (g x)

  -- nondependent function composition
  _∘'_ : ∀ {a b c}
    → {A : Set a} {B : Set b} {C : Set c}
    → (B  → C) → (A → B) → (A → C)
  (f ∘' g) x = f (g x)

open Function public

module Product where
  -- dependent product
  infixr 60 _,_

  record Σ {i j} (A : Type i) (B : A → Type j) : Type (lmax i j) where
    constructor _,_
    field
      fst : A
      snd : B fst
  open Σ public

  _×_ : ∀ {α β} (A : Set α) (B : Set β) → Set (lmax α β)
  A × B = Σ A (λ _ → B)

open Product public

module Nat where
  data ℕ : Set where
    zero : ℕ
    suc  : (n : ℕ) → ℕ

  {-# BUILTIN NATURAL ℕ #-}

open Nat public
