{-# OPTIONS --without-K #-}

module ch1.ex14 where

open import HottPrelude

{-

Why do the induction principles for identity types not allow us to construct a
function

f : ∏(x:A) ∏(p:x=x)(p = refl_x)

with the defining equation

f (x, reflx ) := refl_refl_x ?

-}

{-

f : (x : A) → (p : x ≡ x) → (p ≡ idp)

(based) path induction requires (at least one of) the endpoints to be free.

topologically, this is what i think is going on (though i am not sure.)

first off, path induction is (moraly) equivalent to (a constructive) CHP
(covering homotopy property, e.g. lifting of paths.)  this is covered in
Awodey-Warren.  basically

recursor = introduction
induction = elimination (+ conversion?)




given a
space A, form the fibration P → A whose fiber P_x over x : A is the loop space
based at x.  (i suppose this is homotopy equivalent to the fundamental
groupiod.)  in each fibre (loop space) there is the distinguished trivial loop
(refl_x.)  for each loop l : P_x, consider the path space from l to refl_x.  we
have a section over


as a counterexample, let A be S^1.  then the fibration is homotopy equivalent to
the universal cover, the fibre over each point is ℤ.  over each point in S^1
there is a distinguished point in the cover which represents the trivial loop.
these points

-}
