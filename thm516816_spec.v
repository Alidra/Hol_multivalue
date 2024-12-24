Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem516816 : forall m : nat, forall n : nat, ((Nat.mul m n) = 0) = ((m = 0) \/ (n = 0)).
