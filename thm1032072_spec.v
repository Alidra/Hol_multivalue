Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1032072 : forall (a : nat), (Nat.mul a (NUMERAL (BIT1 0))) = a.
