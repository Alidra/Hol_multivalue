Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem76380 : ((BIT0 (NUMERAL 0)) = (NUMERAL 0)) /\ (forall n : nat, (BIT0 (S n)) = (S (S (BIT0 n)))).
