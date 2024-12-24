Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem302781 : forall (m : nat) (n : nat), (m = n) = ((Nat.mul (NUMERAL (BIT0 (BIT1 0))) m) = (Nat.mul (NUMERAL (BIT0 (BIT1 0))) n)).
