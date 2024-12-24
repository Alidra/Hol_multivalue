Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem84913 : forall m : nat, forall n : nat, forall p : nat, ((Nat.mul m p) = (Nat.mul n p)) = ((m = n) \/ (p = (NUMERAL 0))).
