Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem7626934 : forall {A N : Type'}, forall i : nat, exists k : nat, (Peano.le (NUMERAL (BIT1 0)) k) /\ ((Peano.le k (@dimindex N (@UNIV N))) /\ (forall x : cart A N, (@dollar A N x i) = (@dollar A N x k))).
