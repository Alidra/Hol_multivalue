Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem516863 : forall n : nat, (Nat.add n n) = (Nat.mul (NUMERAL (BIT0 (BIT1 0))) n).
