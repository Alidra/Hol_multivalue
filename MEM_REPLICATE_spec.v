Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1139083 : forall {A : Type'}, forall n : nat, forall x : A, forall y : A, (@List.In A x (@repeat_with_perm_args A n y)) = ((x = y) /\ (~ (n = (NUMERAL 0)))).
