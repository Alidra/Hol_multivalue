Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem7119665 : forall {A : Type'}, forall u : A -> real, forall s : A -> Prop, ((@FINITE A s) /\ ((@sum A s u) = (real_of_num (NUMERAL 0)))) -> (forall i : A, (@IN A i s) -> (u i) = (real_of_num (NUMERAL 0))) \/ (exists j : A, exists k : A, (@IN A j s) /\ ((real_lt (u j) (real_of_num (NUMERAL 0))) /\ ((@IN A k s) /\ (real_gt (u k) (real_of_num (NUMERAL 0)))))).
