Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem210692 : forall n : nat, (~ (n = (NUMERAL 0))) -> (Nat.div n n) = (NUMERAL (BIT1 0)).
