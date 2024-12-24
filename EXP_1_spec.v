Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem88010 : forall n : nat, (Nat.pow n (NUMERAL (BIT1 0))) = n.
