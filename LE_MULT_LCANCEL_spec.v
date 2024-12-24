Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem104208 : forall m : nat, forall n : nat, forall p : nat, (Peano.le (Nat.mul m n) (Nat.mul m p)) = ((m = (NUMERAL 0)) \/ (Peano.le n p)).
