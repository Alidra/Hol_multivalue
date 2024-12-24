Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem182043 : forall n : nat, (Nat.div n (NUMERAL (BIT1 0))) = n.
