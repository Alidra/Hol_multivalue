Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem92678 : forall m : nat, forall n : nat, ~ ((Peano.lt m n) /\ (Peano.lt n m)).
