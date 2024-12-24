Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem89994 : (forall m : nat, (Peano.lt m (NUMERAL 0)) = False) /\ (forall m : nat, forall n : nat, (Peano.lt m (S n)) = ((m = n) \/ (Peano.lt m n))).
