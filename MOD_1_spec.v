Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem182042 : forall n : nat, (Nat.modulo n (NUMERAL (BIT1 0))) = (NUMERAL 0).
