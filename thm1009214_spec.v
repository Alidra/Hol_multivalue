Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1009214 : forall (m : nat) (n : nat), ((Nat.pow (NUMERAL m) (NUMERAL n)) = (Nat.pow m n)) = ((Nat.pow (NUMERAL m) (NUMERAL n)) = (Nat.pow m n)).
