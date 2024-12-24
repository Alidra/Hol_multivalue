Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem7640394 : forall {M N : Type'}, (@FINITE (finite_sum M N) (@UNIV (finite_sum M N))) /\ ((@CARD (finite_sum M N) (@UNIV (finite_sum M N))) = (Nat.add (@dimindex M (@UNIV M)) (@dimindex N (@UNIV N)))).
