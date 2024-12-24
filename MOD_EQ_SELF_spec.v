Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem173992 : forall m : nat, forall n : nat, ((Nat.modulo m n) = m) = ((n = (NUMERAL 0)) \/ (Peano.lt m n)).
