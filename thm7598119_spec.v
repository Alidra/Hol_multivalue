Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem7598119 : forall {A : Type'} (n : nat), (~ ((@HAS_SIZE A (@UNIV A) n) -> (@dimindex A (@UNIV A)) = n)) -> False.
