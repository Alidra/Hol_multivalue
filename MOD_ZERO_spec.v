Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem159121 : forall n : nat, (Nat.modulo n (NUMERAL 0)) = n.
