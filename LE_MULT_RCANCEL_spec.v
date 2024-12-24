Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem104289 : forall m : nat, forall n : nat, forall p : nat, (Peano.le (Nat.mul m p) (Nat.mul n p)) = ((Peano.le m n) \/ (p = (NUMERAL 0))).
