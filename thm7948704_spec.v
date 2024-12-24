Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem7948704 : forall {A : Type'} (n : nat), (((@dimindex A (@UNIV A)) = n) = ((@dimindex (tybit0 A) (@UNIV (tybit0 A))) = (BIT0 n))) /\ ((((@dimindex A (@UNIV A)) = n) = ((@dimindex (tybit1 A) (@UNIV (tybit1 A))) = (BIT1 n))) /\ ((@dimindex unit (@UNIV unit)) = (BIT1 0))).
