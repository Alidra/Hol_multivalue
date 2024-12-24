Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem200698 : forall n : nat, (Nat.modulo n n) = (NUMERAL 0).
