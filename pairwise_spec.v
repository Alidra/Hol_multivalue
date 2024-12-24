Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem4794393 : forall {_110510 : Type'}, forall s : _110510 -> Prop, forall r : _110510 -> _110510 -> Prop, (@pairwise _110510 r s) = (forall x : _110510, forall y : _110510, ((@IN _110510 x s) /\ ((@IN _110510 y s) /\ (~ (x = y)))) -> r x y).
