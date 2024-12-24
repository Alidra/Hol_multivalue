Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem3112385 : forall m : nat, forall n : nat, (num_divides m n) = ((Nat.modulo n m) = (NUMERAL 0)).
