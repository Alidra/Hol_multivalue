Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1008952 : forall (m : nat) (p : nat), ((Nat.pow m (NUMERAL (BIT0 (BIT1 0)))) = p) = ((Nat.mul (NUMERAL m) (NUMERAL m)) = (NUMERAL p)).
