Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem7604549 : forall {A : Type'}, forall x : finite_image A, exists x' : nat, (x = (@finite_index A x')) /\ (@IN nat x' (dotdot (NUMERAL (BIT1 0)) (@dimindex A (@UNIV A)))).
