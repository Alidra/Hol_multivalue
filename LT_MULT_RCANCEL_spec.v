Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem105963 : forall m : nat, forall n : nat, forall p : nat, (Peano.lt (Nat.mul m p) (Nat.mul n p)) = ((Peano.lt m n) /\ (~ (p = (NUMERAL 0)))).
