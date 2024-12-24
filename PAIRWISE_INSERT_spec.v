Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem4807107 : forall {_110698 : Type'}, forall r : _110698 -> _110698 -> Prop, forall x : _110698, forall s : _110698 -> Prop, (@pairwise _110698 r (@INSERT _110698 x s)) = ((forall y : _110698, ((@IN _110698 y s) /\ (~ (y = x))) -> (r x y) /\ (r y x)) /\ (@pairwise _110698 r s)).
