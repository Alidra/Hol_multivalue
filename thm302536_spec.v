Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem302536 : forall (n : nat), (~ ((S n) = (NUMERAL 0))) -> ((S n) = (NUMERAL 0)) = False.
