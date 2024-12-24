Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem196469 : forall m : nat, forall n : nat, (~ (n = (NUMERAL 0))) -> (Nat.div (Nat.modulo m n) n) = (NUMERAL 0).
