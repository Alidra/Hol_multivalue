Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem135734 : forall n : nat, (Nat.sub n n) = (NUMERAL 0).
