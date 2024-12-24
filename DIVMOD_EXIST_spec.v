Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem154676 : forall m : nat, forall n : nat, (~ (n = (NUMERAL 0))) -> exists q : nat, exists r : nat, (m = (Nat.add (Nat.mul q n) r)) /\ (Peano.lt r n).
