Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem3086875 : forall m : nat, forall n : nat, (num_divides m n) -> ((Peano.le (NUMERAL (BIT1 0)) m) /\ (Peano.le m n)) \/ (n = (NUMERAL 0)).
