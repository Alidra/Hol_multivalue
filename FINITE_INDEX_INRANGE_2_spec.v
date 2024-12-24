Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem7629768 : forall {A B N : Type'}, forall i : nat, exists k : nat, (Peano.le (NUMERAL (BIT1 0)) k) /\ ((Peano.le k (@dimindex N (@UNIV N))) /\ ((forall x : cart A N, (@dollar A N x i) = (@dollar A N x k)) /\ (forall y : cart B N, (@dollar B N y i) = (@dollar B N y k)))).
