Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem86997 : forall m : nat, forall n : nat, ((Nat.pow m n) = (NUMERAL 0)) = ((m = (NUMERAL 0)) /\ (~ (n = (NUMERAL 0)))).
