{-# OPTIONS --without-K #-}

open import HottPrelude

module ch2.ex6 {i} {A : Type i} {x y z : A} where

{-

Prove that if p : x ≡ y, then the function (p ∙ _) : (y ≡ z) → (x ≡ z) is an
equivalence.

-}

--foo : (p : x ≡ y) (q : x ≡ z) → p ∙ ! p ∙ q ≡ q
--foo p idp = ?

ex6-f-g : (p : x ≡ y) (q : x ≡ z) → p ∙ ! p ∙ q ≡ q
ex6-f-g p q = ! (∙-assoc p (! p) q) ∙ ap (λ t → t ∙ q) (!-inv-r p)

ex6-g-f : (p : x ≡ y) (q : y ≡ z) → ! p ∙ p ∙ q ≡ q
ex6-g-f p q = ! (∙-assoc (! p) p q) ∙ ap (λ t → t ∙ q) (!-inv-l p)

ex6 : (p : x ≡ y) → is-equiv (_∙_ p)
ex6 p = is-eq (_∙_ p) (_∙_ (! p)) (ex6-f-g p) (ex6-g-f p)
