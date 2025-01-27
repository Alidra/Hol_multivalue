Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem302598 : forall (m : nat) (n : nat), ((m = n) = ((Nat.add m m) = (Nat.mul (NUMERAL (BIT0 (BIT1 0))) n))) = ((m = n) = ((BIT0 m) = (Nat.mul (NUMERAL (BIT0 (BIT1 0))) n))).
