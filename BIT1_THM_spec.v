Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem80210 : forall n : nat, (NUMERAL (BIT1 n)) = (S (Nat.add (NUMERAL n) (NUMERAL n))).
