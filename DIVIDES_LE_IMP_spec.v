Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem3088029 : forall m : nat, forall n : nat, ((num_divides m n) /\ ((n = (NUMERAL 0)) -> m = (NUMERAL 0))) -> Peano.le m n.
