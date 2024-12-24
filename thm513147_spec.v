Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem513147 : forall (n : nat), (~ ((S n) = 0)) -> ((S n) = 0) = False.
