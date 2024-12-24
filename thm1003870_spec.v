Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1003870 : forall (m : nat) (p : nat), ((Nat.pow m (NUMERAL (BIT0 (BIT1 0)))) = p) = ((Nat.mul m m) = p).
