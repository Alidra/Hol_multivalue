Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem170049 : (forall n : nat, (Nat.div (NUMERAL 0) n) = (NUMERAL 0)) /\ (forall n : nat, (Nat.modulo (NUMERAL 0) n) = (NUMERAL 0)).
