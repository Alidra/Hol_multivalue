Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem719454 : forall (n : nat), ((fun n' : nat => (S (BIT1 n')) = (BIT0 (S n'))) n) = ((S (BIT1 n)) = (BIT0 (S n))).
