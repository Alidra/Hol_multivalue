Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem150395 : forall x : nat, forall m : nat, forall n : nat, ((Nat.pow x m) = (Nat.pow x n)) = (@COND Prop (x = (NUMERAL 0)) ((m = (NUMERAL 0)) = (n = (NUMERAL 0))) ((x = (NUMERAL (BIT1 0))) \/ (m = n))).
