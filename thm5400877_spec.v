Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem5400877 : forall (m : nat) (n : nat) (h1 : ~ (Peano.le m (S n))), ~ (Peano.le m (S n)).
