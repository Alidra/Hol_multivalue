Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1007663 : forall (m : nat) (n : nat) (p : nat), ((Nat.mul m n) = p) = ((Nat.mul (NUMERAL m) (NUMERAL n)) = (NUMERAL p)).
