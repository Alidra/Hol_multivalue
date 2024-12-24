Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem87885 : forall n : nat, (Nat.pow (NUMERAL (BIT1 0)) n) = (NUMERAL (BIT1 0)).
