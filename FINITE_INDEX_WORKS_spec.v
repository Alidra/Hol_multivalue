Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem7609879 : forall {A : Type'}, forall i : finite_image A, @ex1 nat (fun n : nat => (Peano.le (NUMERAL (BIT1 0)) n) /\ ((Peano.le n (@dimindex A (@UNIV A))) /\ ((@finite_index A n) = i))).
