Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem137156 : forall n : nat, (Nat.sub (S n) (NUMERAL (BIT1 0))) = n.
