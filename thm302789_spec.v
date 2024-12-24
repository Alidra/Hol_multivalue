Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem302789 : forall (m : nat) (n : nat), (m = n) = ((BIT0 m) = (Nat.mul (NUMERAL (BIT0 (BIT1 0))) n)).
