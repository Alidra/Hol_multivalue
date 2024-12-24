Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem3137141 : forall (a : nat) (b : nat), (num_coprime (@pair nat nat a b)) = (forall d : nat, ((num_divides d a) /\ (num_divides d b)) -> d = (NUMERAL (BIT1 0))).
