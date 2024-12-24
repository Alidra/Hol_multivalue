Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1032046 : forall (x : nat), (Nat.mul (NUMERAL (BIT1 0)) x) = x.
