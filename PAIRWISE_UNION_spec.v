Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem4821878 : forall {_110859 : Type'}, forall R : _110859 -> _110859 -> Prop, forall s : _110859 -> Prop, forall t : _110859 -> Prop, (@pairwise _110859 R (@UNION _110859 s t)) = ((@pairwise _110859 R s) /\ ((@pairwise _110859 R t) /\ (forall x : _110859, forall y : _110859, ((@IN _110859 x (@DIFF _110859 s t)) /\ (@IN _110859 y (@DIFF _110859 t s))) -> (R x y) /\ (R y x)))).
