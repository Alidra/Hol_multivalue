Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem199160 : forall m : nat, forall n : nat, ((Nat.modulo m n) = (NUMERAL 0)) = (exists q : nat, m = (Nat.mul q n)).
