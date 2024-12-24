Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem523715 : forall n : nat, ~ ((Nat.pow (NUMERAL (BIT0 (BIT1 0))) n) = (NUMERAL 0)).
