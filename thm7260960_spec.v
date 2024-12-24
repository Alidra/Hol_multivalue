Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem7260960 : forall {_132349 : Type'} (f : _132349 -> real) (s : _132349 -> Prop) (g : _132349 -> real), ((fun g' : _132349 -> real => (forall x : _132349, (@IN _132349 x s) -> (f x) = (g' x)) -> (@sum _132349 s f) = (@sum _132349 s g')) g) = ((forall x : _132349, (@IN _132349 x s) -> (f x) = (g x)) -> (@sum _132349 s f) = (@sum _132349 s g)).
